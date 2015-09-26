pub mod syntax;
pub mod unify;

pub mod solve;

pub mod parser; // lalrpop generated parser
use solve::{solve_toplevel};

extern crate lalrpop_util;
extern crate readline;
use readline::readline;
use std::ffi::CString;

fn main() {
    use syntax::Database;
    use syntax::ToplevelCmd::*;
    use parser::parse_Toplevel;
    use std::str;
    use lalrpop_util::ParseError;

    let mut db: Database = vec![];

    println!("Welcome to miniprolog!");

    let prompt = CString::new("miniprolog> ").unwrap();

    while let Ok(s) = readline(&prompt) {
      match parse_Toplevel(str::from_utf8(s.to_bytes()).unwrap()) {
        Ok(commands)  =>
          for &ref command in commands.iter() {
            match command {
              &Assert(ref a) => db.push(a.clone()),
              &Goal(ref g)   => solve_toplevel(&db, &g),
              &Quit          => return,
              &Use(_)        => return
            }
          },
        Err(_) => println!("Parse error")
    }
  }
}
