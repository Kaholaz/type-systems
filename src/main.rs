pub mod ast;
pub mod parser;
pub mod runtime;

fn main() {
    match parser::parse("x=y".to_string()) {
        Ok(_) => {
            print!("yes");
        }
        Err(e) => {
            dbg!(e);
        }
    }
}
