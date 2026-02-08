use clap::{Parser, ValueEnum};
use proc_macro2::Ident;
use quote::ToTokens;
use rand::{distr::Alphanumeric, rngs::SmallRng, Rng, SeedableRng};
use ra_ap_ide::{AnalysisHost, FilePosition, RenameConfig, SourceChange};
use ra_ap_ide_db::FileId;
use ra_ap_ide_db::text_edit::TextEdit;
use ra_ap_load_cargo::{load_workspace_at, LoadCargoConfig, ProcMacroServerChoice};
use ra_ap_project_model::CargoConfig;
use ra_ap_syntax::{ast, AstNode, TextRange};
use ra_ap_syntax::ast::{HasAttrs, HasModuleItem, HasName, HasVisibility};
use regex::{Captures, Regex};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::PathBuf;
use syn::visit_mut::{self, VisitMut};
use walkdir::WalkDir;

fn is_ignored_entry(entry: &walkdir::DirEntry) -> bool {
    let name = entry.file_name().to_string_lossy();
    if name.as_ref() == "target" && is_vendor_path(entry.path()) {
        return false;
    }
    matches!(name.as_ref(), ".git" | "target" | "node_modules")
}

fn is_vendor_path(path: &std::path::Path) -> bool {
    path.components()
        .any(|component| component.as_os_str() == "vendor")
}

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Input directory (source code to obfuscate)
    #[arg(short, long)]
    input: PathBuf,

    /// Output directory (where obfuscated code will be saved)
    #[arg(short, long)]
    output: PathBuf,

    /// Strip PII (emails, local paths) and configure binary stripping
    #[arg(long)]
    strip_pii: bool,

    /// Obfuscation mode
    #[arg(long, value_enum, default_value_t = Mode::Safe)]
    mode: Mode,

    /// Deterministic seed (hex or decimal)
    #[arg(long)]
    seed: Option<u64>,
}

#[derive(Copy, Clone, Debug, ValueEnum)]
enum Mode {
    Safe,
    Aggressive,
}

struct Obfuscator {
    mapping: HashMap<String, String>,
    protected_names: HashSet<String>,
    internal_definitions: HashSet<String>,
    strip_pii: bool,
    mode: Mode,
    rng: SmallRng,
    pattern_depth: usize,
}

struct RustRenamePlan {
    edits_by_path: HashMap<PathBuf, TextEdit>,
    renamed: usize,
    skipped: usize,
}

struct RenameTarget {
    file_id: FileId,
    range: TextRange,
    name: String,
}

impl Obfuscator {
    fn new(strip_pii: bool, mode: Mode, seed: Option<u64>) -> Self {
        let mut protected_names = HashSet::new();
        let keywords = [
            "as", "break", "const", "continue", "crate", "else", "enum", "extern", "false", "fn",
            "for", "if", "impl", "in", "let", "loop", "match", "mod", "move", "mut", "pub", "ref",
            "return", "self", "Self", "static", "struct", "super", "trait", "true", "type",
            "unsafe", "use", "where", "while", "async", "await", "dyn", "abstract", "become",
            "box", "do", "final", "macro", "override", "priv", "typeof", "unsized", "virtual",
            "yield", "try", "main",
        ];
        for k in keywords {
            protected_names.insert(k.to_string());
        }

        let common = [
            "String", "Option", "Result", "Some", "None", "Ok", "Err", "Vec", "Box", "rc", "Arc",
            "panic", "println", "print", "format", "vec", "std", "core", "alloc", "anyhow", "clap",
        ];
        for c in common {
            protected_names.insert(c.to_string());
        }

        let attrs = [
            "allow",
            "cfg",
            "cfg_attr",
            "derive",
            "path",
            "macro_use",
            "macro_export",
            "test",
            "ignore",
            "should_panic",
            "doc",
            "no_mangle",
            "export_name",
            "link_name",
            "repr",
            "inline",
            "cold",
            "track_caller",
            "deprecated",
            "must_use",
        ];
        for a in attrs {
            protected_names.insert(a.to_string());
        }

        let rng = match seed {
            Some(seed) => SmallRng::seed_from_u64(seed),
            None => {
                let mut rng = rand::rng();
                SmallRng::from_rng(&mut rng)
            }
        };

        Self {
            mapping: HashMap::new(),
            protected_names,
            internal_definitions: HashSet::new(),
            strip_pii,
            mode,
            rng,
            pattern_depth: 0,
        }
    }

    fn generate_random_name(&mut self) -> String {
        let len = self.rng.random_range(12..24);
        let name: String = (0..len)
            .map(|_| self.rng.sample(Alphanumeric) as char)
            .collect::<String>()
            .to_lowercase();
        let first: char = self.rng.random_range(b'a'..=b'z') as char;
        format!("{}{}", first, name)
    }

    fn obfuscate_name(&mut self, original: &str) -> String {
        if self.protected_names.contains(original) {
            return original.to_string();
        }

        if !self.internal_definitions.contains(original) && !self.mapping.contains_key(original) {
            return original.to_string();
        }

        if let Some(obfuscated) = self.mapping.get(original) {
            obfuscated.clone()
        } else {
            let obfuscated = self.generate_random_name();
            self.mapping
                .insert(original.to_string(), obfuscated.clone());
            obfuscated
        }
    }

    fn strip_pii_content(&self, content: &str) -> String {
        let mut result = content.to_string();

        // Remove emails
        let email_regex = Regex::new(r"[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}").unwrap();
        result = email_regex
            .replace_all(&result, "user@example.com")
            .to_string();

        // Remove local unix paths (e.g., /home/username/...)
        let path_regex = Regex::new(r"/[a-zA-Z0-9\._\-]+(/[a-zA-Z0-9\._\-]+)+").unwrap();
        result = path_regex
            .replace_all(&result, |caps: &Captures| {
                let path = &caps[0];
                if path.starts_with("/home/") || path.starts_with("/Users/") {
                    "/redacted/path".to_string()
                } else {
                    path.to_string()
                }
            })
            .to_string();

        result
    }

    fn plan_rust_renames(&mut self, input_root: &std::path::Path) -> anyhow::Result<RustRenamePlan> {
        let cargo_config = CargoConfig { set_test: true, ..CargoConfig::default() };
        let load_config = LoadCargoConfig {
            load_out_dirs_from_check: false,
            with_proc_macro_server: ProcMacroServerChoice::None,
            prefill_caches: false,
        };
        let (db, vfs, _proc_macros) =
            load_workspace_at(input_root, &cargo_config, &load_config, &|_| {})?;
        let analysis = AnalysisHost::with_database(db).analysis();
        let input_root = fs::canonicalize(input_root)?;

        let mut seen_targets: HashSet<(FileId, TextRange)> = HashSet::new();
        let mut used_names = self.protected_names.clone();
        let mut changes = SourceChange::default();
        let mut renamed = 0usize;
        let mut skipped = 0usize;
        let rename_config = RenameConfig {
            prefer_no_std: false,
            prefer_prelude: false,
            prefer_absolute: false,
            show_conflicts: false,
        };

        for (file_id, path) in vfs.iter() {
            let Some(real_path) = path.as_path() else {
                continue;
            };
            let real_path: PathBuf =
                <ra_ap_paths::AbsPath as AsRef<std::path::Path>>::as_ref(real_path).to_path_buf();
            if !real_path.starts_with(&input_root) {
                continue;
            }
            if real_path.extension().and_then(|s| s.to_str()) != Some("rs") {
                continue;
            }
            if analysis.is_library_file(file_id).unwrap_or(true) {
                continue;
            }
            let Ok(source_file) = analysis.parse(file_id) else {
                continue;
            };
            let targets = self.collect_rename_targets(file_id, &source_file);
            for target in targets {
                if !seen_targets.insert((target.file_id, target.range)) {
                    continue;
                }
                if !self.should_obfuscate_name(&target.name) {
                    skipped += 1;
                    continue;
                }
                let new_name = match self.generate_unique_name(&mut used_names) {
                    Some(name) => name,
                    None => {
                        skipped += 1;
                        continue;
                    }
                };
                let position = FilePosition { file_id: target.file_id, offset: target.range.start() };
                let rename_result = analysis.rename(position, &new_name, &rename_config);
                let Ok(rename_result) = rename_result else {
                    skipped += 1;
                    continue;
                };
                let Ok(change) = rename_result else {
                    skipped += 1;
                    continue;
                };
                changes = changes.merge(change);
                renamed += 1;
            }
        }

        let mut edits_by_path = HashMap::new();
        for (file_id, (edit, _)) in changes.source_file_edits {
            let Some(path) = vfs.file_path(file_id).as_path() else {
                continue;
            };
            let real_path: PathBuf =
                <ra_ap_paths::AbsPath as AsRef<std::path::Path>>::as_ref(path).to_path_buf();
            if real_path.starts_with(&input_root) {
                edits_by_path.insert(real_path, edit);
            }
        }

        Ok(RustRenamePlan { edits_by_path, renamed, skipped })
    }

    fn should_obfuscate_name(&self, name: &str) -> bool {
        if name == "_" {
            return false;
        }
        if self.protected_names.contains(name) {
            return false;
        }
        true
    }

    fn generate_unique_name(&mut self, used: &mut HashSet<String>) -> Option<String> {
        for _ in 0..32 {
            let name = self.generate_random_name();
            if self.protected_names.contains(&name) || used.contains(&name) {
                continue;
            }
            used.insert(name.clone());
            return Some(name);
        }
        None
    }

    fn collect_rename_targets(&self, file_id: FileId, source_file: &ast::SourceFile) -> Vec<RenameTarget> {
        let mut targets = Vec::new();

        for item in source_file.items() {
            match item {
                ast::Item::Fn(node) => {
                    if !self.item_is_public(&node) && !self.has_protected_attr(&node) {
                        self.push_named_target(file_id, node.name(), &mut targets);
                    }
                }
                ast::Item::Struct(node) => {
                    if !self.item_is_public(&node) && !self.has_protected_attr(&node) {
                        self.push_named_target(file_id, node.name(), &mut targets);
                    }
                }
                ast::Item::Enum(node) => {
                    if !self.item_is_public(&node) && !self.has_protected_attr(&node) {
                        self.push_named_target(file_id, node.name(), &mut targets);
                    }
                }
                ast::Item::Trait(node) => {
                    if !self.item_is_public(&node) && !self.has_protected_attr(&node) {
                        self.push_named_target(file_id, node.name(), &mut targets);
                    }
                }
                ast::Item::TypeAlias(node) => {
                    if !self.item_is_public(&node) && !self.has_protected_attr(&node) {
                        self.push_named_target(file_id, node.name(), &mut targets);
                    }
                }
                ast::Item::Const(node) => {
                    if !self.item_is_public(&node) && !self.has_protected_attr(&node) {
                        self.push_named_target(file_id, node.name(), &mut targets);
                    }
                }
                ast::Item::Static(node) => {
                    if !self.item_is_public(&node) && !self.has_protected_attr(&node) {
                        self.push_named_target(file_id, node.name(), &mut targets);
                    }
                }
                ast::Item::Union(node) => {
                    if !self.item_is_public(&node) && !self.has_protected_attr(&node) {
                        self.push_named_target(file_id, node.name(), &mut targets);
                    }
                }
                _ => {}
            }
        }

        for assoc in source_file.syntax().descendants().filter_map(ast::AssocItem::cast) {
            match assoc {
                ast::AssocItem::Fn(node) => {
                    if !self.item_is_public(&node) && !self.has_protected_attr(&node) {
                        self.push_named_target(file_id, node.name(), &mut targets);
                    }
                }
                ast::AssocItem::Const(node) => {
                    if !self.item_is_public(&node) && !self.has_protected_attr(&node) {
                        self.push_named_target(file_id, node.name(), &mut targets);
                    }
                }
                ast::AssocItem::TypeAlias(node) => {
                    if !self.item_is_public(&node) && !self.has_protected_attr(&node) {
                        self.push_named_target(file_id, node.name(), &mut targets);
                    }
                }
                _ => {}
            }
        }

        for field in source_file.syntax().descendants().filter_map(ast::RecordField::cast) {
            if self.item_is_public(&field) {
                continue;
            }
            self.push_named_target(file_id, field.name(), &mut targets);
        }

        for variant in source_file.syntax().descendants().filter_map(ast::Variant::cast) {
            if self.variant_is_public(&variant) {
                continue;
            }
            self.push_named_target(file_id, variant.name(), &mut targets);
        }

        for pat in source_file.syntax().descendants().filter_map(ast::IdentPat::cast) {
            self.push_named_target(file_id, pat.name(), &mut targets);
        }

        targets
    }

    fn push_named_target(
        &self,
        file_id: FileId,
        name: Option<ast::Name>,
        targets: &mut Vec<RenameTarget>,
    ) {
        let Some(name) = name else {
            return;
        };
        let Some(text) = self.name_text(&name) else {
            return;
        };
        let range = name.syntax().text_range();
        targets.push(RenameTarget {
            file_id,
            range,
            name: text,
        });
    }

    fn name_text(&self, name: &ast::Name) -> Option<String> {
        if let Some(token) = name.ident_token() {
            return Some(token.text().to_string());
        }
        if let Some(token) = name.self_token() {
            return Some(token.text().to_string());
        }
        None
    }

    fn item_is_public<T: HasVisibility>(&self, node: &T) -> bool {
        node.visibility().and_then(|v| v.pub_token()).is_some()
    }

    fn has_protected_attr<T: HasAttrs>(&self, node: &T) -> bool {
        let protected = ["no_mangle", "export_name", "link_name"];
        node.attrs().filter_map(|attr| self.attr_name(&attr)).any(|name| {
            protected.iter().any(|protected_name| name == *protected_name)
        })
    }

    fn attr_name(&self, attr: &ast::Attr) -> Option<String> {
        let path = attr.meta()?.path()?;
        let segment = path.segment()?;
        let name_ref = segment.name_ref()?;
        let token = name_ref.ident_token()?;
        Some(token.text().to_string())
    }

    fn variant_is_public(&self, variant: &ast::Variant) -> bool {
        if self.item_is_public(variant) {
            return true;
        }
        for ancestor in variant.syntax().ancestors() {
            if let Some(parent_enum) = ast::Enum::cast(ancestor) {
                return self.item_is_public(&parent_enum);
            }
        }
        false
    }

    fn process_rust(&mut self, content: &str) -> String {
        let content = if self.strip_pii {
            self.strip_pii_content(content)
        } else {
            content.to_string()
        };

        let mut syntax_tree: syn::File = match syn::parse_str(&content) {
            Ok(file) => file,
            Err(_) => return content,
        };

        self.visit_file_mut(&mut syntax_tree);
        syntax_tree.to_token_stream().to_string()
    }

    fn process_html(&mut self, content: &str) -> String {
        let content = if self.strip_pii {
            self.strip_pii_content(content)
        } else {
            content.to_string()
        };

        if matches!(self.mode, Mode::Safe) {
            return content;
        }

        let mut result = content;
        let re_comment = Regex::new(r"(?s)<!--.*?-->").unwrap();
        result = re_comment.replace_all(&result, "").to_string();
        let re_between_tags = Regex::new(r">\s+<").unwrap();
        result = re_between_tags.replace_all(&result, "><").to_string();
        let re_whitespace = Regex::new(r"\s{2,}").unwrap();
        result = re_whitespace.replace_all(&result, " ").to_string();
        result
    }

    fn process_js(&mut self, content: &str) -> String {
        let content = if self.strip_pii {
            self.strip_pii_content(content)
        } else {
            content.to_string()
        };

        if matches!(self.mode, Mode::Safe) {
            return content;
        }

        let mut result = content;
        let re_comment = Regex::new(r"(?s)/\*.*?\*/").unwrap();
        result = re_comment.replace_all(&result, "").to_string();
        let re_line_comment = Regex::new(r"(?m)//.*$").unwrap();
        result = re_line_comment.replace_all(&result, "").to_string();
        let re_whitespace = Regex::new(r"[ \t]{2,}").unwrap();
        result = re_whitespace.replace_all(&result, " ").to_string();
        let re_lines = Regex::new(r"\n{2,}").unwrap();
        result = re_lines.replace_all(&result, "\n").to_string();
        result
    }

    fn process_css(&mut self, content: &str) -> String {
        let content = if self.strip_pii {
            self.strip_pii_content(content)
        } else {
            content.to_string()
        };

        if matches!(self.mode, Mode::Safe) {
            return content;
        }

        let mut result = content;
        let re_comment = Regex::new(r"(?s)/\*.*?\*/").unwrap();
        result = re_comment.replace_all(&result, "").to_string();
        let re_punct = Regex::new(r"\s*([{}:;,])\s*").unwrap();
        result = re_punct.replace_all(&result, "$1").to_string();
        let re_whitespace = Regex::new(r"[ \t]{2,}").unwrap();
        result = re_whitespace.replace_all(&result, " ").to_string();
        result
    }

    fn process_cargo_toml(&self, content: &str) -> String {
        let mut result = content.to_string();
        if self.strip_pii {
            // Remove authors
            let authors_regex = Regex::new(r"(?m)^authors\s*=\s*\[.*?\]").unwrap();
            result = authors_regex
                .replace_all(&result, "authors = []")
                .to_string();

            // Add binary stripping configuration if not present
            if !result.contains("strip = true") {
                result.push_str("\n[profile.release]\nstrip = true\nopt-level = \"z\"\nlto = true\ncodegen-units = 1\n");
            }
        }
        result
    }

    fn insert_dead_code(&mut self, block: &mut syn::Block) {
        if block.stmts.is_empty() || self.rng.random_range(0..3) != 0 {
            return;
        }

        let var_name = format!("_{}", self.generate_random_name());
        let var_ident = Ident::new(&var_name, proc_macro2::Span::call_site());
        let rand_val: i32 = self.rng.random_range(1..1000);

        let dead_stmt: syn::Stmt = syn::parse_quote! {
            let #var_ident = {
                let mut _x = #rand_val;
                _x = _x.wrapping_mul(3).wrapping_add(1);
                _x
            };
        };

        let max_pos = block.stmts.len().saturating_sub(1);
        if block.stmts.len() > 1 {
            let pos = self.rng.random_range(0..max_pos);
            block.stmts.insert(pos, dead_stmt);
        } else {
            block.stmts.insert(0, dead_stmt);
        }
    }

    fn flatten_control_flow(&mut self, block: &mut syn::Block) {
        if block.stmts.len() < 3 || self.rng.random_range(0..5) != 0 {
            return;
        }
        if block
            .stmts
            .iter()
            .any(|stmt| matches!(stmt, syn::Stmt::Local(_)))
        {
            return;
        }
        if !self.block_is_safe_to_flatten(block) {
            return;
        }
        let count = block.stmts.len();
        let mut cases = Vec::new();
        for (idx, stmt) in block.stmts.iter().cloned().enumerate() {
            let index = idx as i32;
            let next = if idx + 1 < count {
                (idx + 1) as i32
            } else {
                -1
            };
            cases.push((index, next, stmt));
        }

        let mut new_stmts = Vec::new();
        let mut match_arms = Vec::new();
        for (index, next, stmt) in cases {
            let mut arm_stmts = Vec::new();
            arm_stmts.push(stmt);
            let assign: syn::Stmt = syn::parse_quote! { state = #next; };
            arm_stmts.push(assign);
            let arm_body = syn::Block {
                brace_token: syn::token::Brace::default(),
                stmts: arm_stmts,
            };
            let pat: syn::Pat = syn::parse_quote! { #index };
            let arm = syn::Arm {
                attrs: Vec::new(),
                pat,
                guard: None,
                fat_arrow_token: syn::token::FatArrow::default(),
                body: Box::new(syn::Expr::Block(syn::ExprBlock {
                    attrs: Vec::new(),
                    label: None,
                    block: arm_body,
                })),
                comma: Some(syn::token::Comma::default()),
            };
            match_arms.push(arm);
        }

        let match_expr = syn::Expr::Match(syn::ExprMatch {
            attrs: Vec::new(),
            match_token: syn::token::Match::default(),
            expr: Box::new(syn::parse_quote! { state }),
            brace_token: syn::token::Brace::default(),
            arms: match_arms,
        });

        let match_stmt = syn::Stmt::Expr(match_expr, Some(syn::token::Semi::default()));
        let loop_block = syn::Block {
            brace_token: syn::token::Brace::default(),
            stmts: vec![match_stmt],
        };
        let loop_expr = syn::Expr::Loop(syn::ExprLoop {
            attrs: Vec::new(),
            label: None,
            loop_token: syn::token::Loop::default(),
            body: loop_block,
        });

        let init_stmt: syn::Stmt = syn::parse_quote! { let mut state = 0i32; };
        new_stmts.push(init_stmt);
        new_stmts.push(syn::Stmt::Expr(
            loop_expr,
            Some(syn::token::Semi::default()),
        ));
        block.stmts = new_stmts;
    }

    fn insert_opaque_predicates(&mut self, block: &mut syn::Block) {
        if block.stmts.len() < 2 || self.rng.random_range(0..4) != 0 {
            return;
        }

        let a: i32 = self.rng.random_range(1..50);
        let b: i32 = self.rng.random_range(1..50);
        let sum = a + b;

        let wrapped_stmts = block.stmts.clone();
        let tokens = quote::quote! {
            {
                if (#a + #b) == #sum {
                    #(#wrapped_stmts);*
                }
            }
        };
        if let Ok(opaque_block) = syn::parse2::<syn::Block>(tokens) {
            block.stmts = opaque_block.stmts;
        }
    }

    fn encode_string_literal(&mut self, value: &str) -> (Vec<u8>, u8) {
        let key: u8 = self.rng.random_range(1..=255);
        let encoded: Vec<u8> = value.bytes().map(|b| b ^ key).collect();
        (encoded, key)
    }

    fn block_is_safe_to_flatten(&self, block: &syn::Block) -> bool {
        for stmt in &block.stmts {
            if let syn::Stmt::Expr(expr, semi) = stmt {
                if semi.is_none() {
                    return false;
                }
                if !self.expr_is_safe_for_flatten(expr) {
                    return false;
                }
            }
        }
        true
    }

    fn expr_is_safe_for_flatten(&self, expr: &syn::Expr) -> bool {
        match expr {
            syn::Expr::Return(_)
            | syn::Expr::Break(_)
            | syn::Expr::Continue(_)
            | syn::Expr::Try(_)
            | syn::Expr::Await(_)
            | syn::Expr::Yield(_) => false,
            syn::Expr::Macro(_) => false,
            syn::Expr::Closure(_) => false,
            syn::Expr::Async(_) => false,
            syn::Expr::Loop(_) => false,
            syn::Expr::While(_) => false,
            syn::Expr::ForLoop(_) => false,
            syn::Expr::Match(_) => false,
            syn::Expr::If(expr_if) => {
                self.expr_is_safe_for_flatten(&expr_if.cond)
                    && self.block_is_safe_to_flatten(&expr_if.then_branch)
                    && expr_if
                        .else_branch
                        .as_ref()
                        .map(|(_, expr)| self.expr_is_safe_for_flatten(expr))
                        .unwrap_or(true)
            }
            syn::Expr::Block(expr_block) => self.block_is_safe_to_flatten(&expr_block.block),
            _ => true,
        }
    }
}

impl RustRenamePlan {
    fn apply(&self, path: &std::path::Path, content: &str) -> String {
        let Ok(real_path) = fs::canonicalize(path) else {
            return content.to_string();
        };
        let Some(edit) = self.edits_by_path.get(&real_path) else {
            return content.to_string();
        };
        let mut updated = content.to_string();
        edit.apply(&mut updated);
        updated
    }
}

impl VisitMut for Obfuscator {
    fn visit_ident_mut(&mut self, i: &mut Ident) {
        let _ = i;
    }

    fn visit_expr_mut(&mut self, expr: &mut syn::Expr) {
        visit_mut::visit_expr_mut(self, expr);

        if let syn::Expr::Lit(expr_lit) = expr {
            if matches!(self.mode, Mode::Aggressive) {
                if let syn::Lit::Str(lit_str) = &expr_lit.lit {
                    if lit_str.value() == "allow" {
                        return;
                    }
                }
            }
            if matches!(self.mode, Mode::Aggressive) {
                if let syn::Lit::Str(lit_str) = &expr_lit.lit {
                    let value = lit_str.value();
                    if !value.is_empty() {
                        let (encoded, key) = self.encode_string_literal(&value);
                        let bytes: Vec<String> =
                            encoded.iter().map(|b| format!("{}u8", b)).collect();
                        let bytes_joined = bytes.join(",");
                        let new_expr: syn::Expr = syn::parse_str(&format!(
                            "{{ let mut v = vec![{}]; for b in &mut v {{ *b ^= {}u8; }} String::from_utf8(v).unwrap() }}",
                            bytes_joined, key
                        ))
                        .unwrap_or_else(|_| expr.clone());
                        *expr = new_expr;
                        return;
                    }
                }
            }
            if let syn::Lit::Int(lit_int) = &expr_lit.lit {
                if self.pattern_depth > 0 {
                    return;
                }
                let suffix = lit_int.suffix();
                if suffix.is_empty() || suffix == "i32" || suffix == "u32" {
                    if let Ok(val) = lit_int.base10_parse::<i64>() {
                        if val > 1 && val < 500 {
                            if self.rng.random_range(0..3) == 0 {
                                let a: i64 = self.rng.random_range(1..val);
                                let b = val - a;
                                let suffix_str = if suffix.is_empty() { "" } else { suffix };
                                let new_expr: syn::Expr = syn::parse_str(&format!(
                                    "({}{}+{}{})",
                                    a, suffix_str, b, suffix_str
                                ))
                                .unwrap_or_else(|_| expr.clone());
                                *expr = new_expr;
                            }
                        }
                    }
                }
            }
        }
    }

    fn visit_block_mut(&mut self, block: &mut syn::Block) {
        visit_mut::visit_block_mut(self, block);
        if matches!(self.mode, Mode::Aggressive) {
            self.insert_dead_code(block);
            self.insert_opaque_predicates(block);
            self.flatten_control_flow(block);
        }
    }

    fn visit_pat_ident_mut(&mut self, i: &mut syn::PatIdent) {
        visit_mut::visit_pat_ident_mut(self, i);
    }

    fn visit_path_mut(&mut self, i: &mut syn::Path) {
        visit_mut::visit_path_mut(self, i);
    }

    fn visit_pat_mut(&mut self, pat: &mut syn::Pat) {
        self.pattern_depth += 1;
        visit_mut::visit_pat_mut(self, pat);
        self.pattern_depth -= 1;
    }

    fn visit_member_mut(&mut self, i: &mut syn::Member) {
        visit_mut::visit_member_mut(self, i);
    }

    fn visit_macro_mut(&mut self, i: &mut syn::Macro) {
        visit_mut::visit_macro_mut(self, i);
    }
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    let mut obfuscator = Obfuscator::new(args.strip_pii, args.mode, args.seed);
    let input_root = fs::canonicalize(&args.input)?;

    if !args.output.exists() {
        fs::create_dir_all(&args.output)?;
    }

    let entries: Vec<_> = WalkDir::new(&input_root)
        .into_iter()
        .filter_entry(|entry| !is_ignored_entry(entry))
        .filter_map(|e| e.ok())
        .collect();

    let rename_plan = match obfuscator.plan_rust_renames(&input_root) {
        Ok(plan) => {
            if plan.renamed > 0 {
                eprintln!(
                    "Rust renames planned: {} applied, {} skipped.",
                    plan.renamed, plan.skipped
                );
            }
            Some(plan)
        }
        Err(err) => {
            eprintln!("Rust rename planning failed: {err}");
            None
        }
    };

    for entry in &entries {
        let path = entry.path();
        if path.is_file() {
            let relative_path = path.strip_prefix(&input_root)?;
            let output_path = args.output.join(relative_path);
            if let Some(parent) = output_path.parent() {
                fs::create_dir_all(parent)?;
            }
            let extension = path.extension().and_then(|s| s.to_str());
            let file_name = path.file_name().and_then(|s| s.to_str());

            match extension {
                _ if is_vendor_path(relative_path) => {
                    fs::copy(path, output_path)?;
                }
                Some("js") | Some("ts") => {
                    let content = fs::read_to_string(path)?;
                    fs::write(output_path, obfuscator.process_js(&content))?;
                }
                Some("html") => {
                    let content = fs::read_to_string(path)?;
                    fs::write(output_path, obfuscator.process_html(&content))?;
                }
                Some("css") => {
                    let content = fs::read_to_string(path)?;
                    fs::write(output_path, obfuscator.process_css(&content))?;
                }
                Some("rs") => {
                    let content = fs::read_to_string(path)?;
                    let content = if let Some(plan) = &rename_plan {
                        plan.apply(path, &content)
                    } else {
                        content
                    };
                    fs::write(output_path, obfuscator.process_rust(&content))?;
                }
                _ => {
                    if file_name == Some("Cargo.toml") {
                        let content = fs::read_to_string(path)?;
                        fs::write(output_path, obfuscator.process_cargo_toml(&content))?;
                    } else {
                        fs::copy(path, output_path)?;
                    }
                }
            }
        }
    }
    Ok(())
}
