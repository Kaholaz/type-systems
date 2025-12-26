use std::{env::args, error::Error, fs::read_to_string};

use crate::runtime::run_program;

pub mod ast;
pub mod parser;
pub mod runtime;
pub mod type_checking;
pub mod util;

fn main() -> Result<(), Box<dyn Error>> {
    let mut args = args();
    args.next();
    let path = args.next().unwrap_or("prelude.tifl".to_string());

    let source = read_to_string(path)?;
    let program = parser::parse(source)?;
    let type_map = type_checking::type_check(&program)?;
    println!("Types:");
    for (symbol, ty) in type_map {
        println!("{}: {}", symbol, ty)
    }

    let values = run_program(&program);
    println!("Values:");
    for (symbol, value) in values {
        println!("{}: {}", symbol, value)
    }
    Ok(())
}
