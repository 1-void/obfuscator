use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use tempfile::TempDir;
use walkdir::WalkDir;

fn copy_tree(src: &Path, dst: &Path) {
    for entry in WalkDir::new(src) {
        let entry = entry.expect("walkdir entry");
        let path = entry.path();
        let rel = path.strip_prefix(src).expect("strip prefix");
        let out = dst.join(rel);
        if entry.file_type().is_dir() {
            fs::create_dir_all(&out).expect("create dir");
            continue;
        }
        if let Some(parent) = out.parent() {
            fs::create_dir_all(parent).expect("create parent dir");
        }
        fs::copy(path, &out).expect("copy file");
    }
}

fn cargo_check(dir: &Path, target_dir: &Path) {
    let status = Command::new("cargo")
        .arg("check")
        .arg("-q")
        .current_dir(dir)
        .env("CARGO_TARGET_DIR", target_dir)
        .status()
        .expect("run cargo check");
    assert!(status.success(), "cargo check failed in {}", dir.display());
}

fn run_obfuscator(input: &Path, output: &Path, args: &[&str]) {
    let exe = env!("CARGO_BIN_EXE_obfuscator");
    let status = Command::new(exe)
        .args(["--input", input.to_str().unwrap()])
        .args(["--output", output.to_str().unwrap()])
        .args(args)
        .status()
        .expect("run obfuscator");
    assert!(status.success(), "obfuscator failed");
}

#[test]
fn e2e_obfuscates_and_output_compiles() {
    let tmp = TempDir::new().expect("tempdir");
    let input = tmp.path().join("input");
    let output = tmp.path().join("output");
    fs::create_dir_all(&input).unwrap();
    fs::create_dir_all(&output).unwrap();

    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    copy_tree(&manifest_dir.join("test_project"), &input);

    run_obfuscator(&input, &output, &["--mode", "safe", "--seed", "1"]);
    cargo_check(&output, &tmp.path().join("cargo-target"));
}

#[test]
fn e2e_strip_pii_rewrites_cargo_toml() {
    let tmp = TempDir::new().expect("tempdir");
    let input = tmp.path().join("input");
    let output = tmp.path().join("output");
    fs::create_dir_all(&input).unwrap();
    fs::create_dir_all(&output).unwrap();

    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    copy_tree(&manifest_dir.join("test_project"), &input);

    run_obfuscator(
        &input,
        &output,
        &["--mode", "safe", "--seed", "1", "--strip-pii"],
    );

    let cargo_toml = fs::read_to_string(output.join("Cargo.toml")).unwrap();
    assert!(cargo_toml.contains("authors = []"), "authors not stripped");
    assert!(
        cargo_toml.contains("[profile.release]") && cargo_toml.contains("strip = true"),
        "release strip profile not added"
    );

    cargo_check(&output, &tmp.path().join("cargo-target"));
}

#[test]
fn e2e_aggressive_output_compiles() {
    let tmp = TempDir::new().expect("tempdir");
    let input = tmp.path().join("input");
    let output = tmp.path().join("output");
    fs::create_dir_all(&input).unwrap();
    fs::create_dir_all(&output).unwrap();

    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    copy_tree(&manifest_dir.join("test_project"), &input);

    run_obfuscator(&input, &output, &["--mode", "aggressive", "--seed", "1"]);
    cargo_check(&output, &tmp.path().join("cargo-target"));
}
