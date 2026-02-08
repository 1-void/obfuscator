struct MyData { field_a: i32 } fn my_function(data: MyData) { println!("{}", data.field_a); } fn main() { let d = MyData { field_a: 10 }; my_function(d); }
