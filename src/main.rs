extern crate lalrpop_util;  // parser generator
extern crate rl_sys;        // provides readline

pub mod syntax;
pub mod unify;
pub mod solve;
pub mod parser; // lalrpop generated parser

use std::fs::File;
use std::io::Error;

use parser::parse_Toplevel;

use solve::{solve_toplevel, assert};
use syntax::Database;
use syntax::ToplevelCmd;
use syntax::ToplevelCmd::*;

enum Status<E> {
  Ok,
  Quit,
  Err(E),
}

/* [exec_cmd cmd] executes the toplevel command [cmd].
   Returns Some() when the computation succeeded and None
   when the command failed.
*/
fn exec_cmd(db: &mut Database, cmd: &ToplevelCmd)
-> Status<Error> {
  match cmd {
    &Assert(ref a) => { assert(db, a.clone());  Status::Ok },
    &Goal(ref g)   => { solve_toplevel(db, &g); Status::Ok },
    &Quit          => Status::Quit,
    &Use(ref file) => match exec_file(db, &file) {
      Status::Err(e) => {
        println!("Failed to execute file {}, {}", file, e);
        /* We could return the error here, but that causes the interpreter
           to quit on every parse error from loading a file */
        Status::Ok
      },
      s => s
    }
  }
}

/* [exec_file fn] executes the contents of file [fn]. */
fn exec_file(db: &mut Database, filename: &String)
-> Status<Error> {
  use std::io::prelude::Read;
  match File::open(filename) {
    Err(e)    => return Status::Err(e),
    Ok(mut f) => {
      let mut s = String::new();
      match f.read_to_string(&mut s) {
        Err(e) => return Status::Err(e),
        Ok(_)  => {
          match parse_Toplevel(&s) {
            Ok(cmds) => exec_cmds(db, &cmds),
            Err(_)   => { println!("Parse error"); Status::Ok }
          }
        }
      }
    }
  }
}

/* [exec_cmds cmds] executes the list of toplevel commands [cmds]. */
fn exec_cmds(db: &mut Database, cmds: &Vec<ToplevelCmd>)
-> Status<Error>
{
  let mut ret : Status<Error> = Status::Ok;
  for &ref cmd in cmds.iter() {
    match exec_cmd(db, cmd) {
      Status::Quit   => { ret = Status::Quit; break },
      Status::Err(e) => { ret = Status::Err(e); break },
      _              => continue
    }
  }
  ret
}

fn main() {
    use rl_sys::{readline, add_history};

    let mut db: Database = vec![];

    println!(r#"Welcome to miniprolog!"#);
    println!(r#"This prolog interpreter is based on the ML code at the PLZoo:"#);
    println!(r#"  http://andrej.com/plzoo/html/miniprolog.html"#);
    println!(r#""#);
    println!(r#"Input syntax: "#);
    println!(r#"    ?- query.            Make a query."#);
    println!(r#"    a(t1, ..., tn).      Assert an atomic proposition."#);
    println!(r#"    A :- B1, ..., Bn.    Assert an inference rule."#);
    println!(r#"    $quit                Exit interpreter."#);
    println!(r#"    $use "filename"      Execute commands from a file."#);

    let prompt = "Prolog> ".to_string();

    while let Some(s) = readline(prompt.clone()) {
      // First add it to the history
      add_history(s.clone());
      match parse_Toplevel(&s) {
        Ok(commands)  => match exec_cmds(&mut db, &commands) {
          Status::Quit   => return,
          Status::Err(e) => {
            println!("Exiting due to unexpected error: {}", e);
            return
          },
          _              => continue
        },
        Err(_)        => println!("Parse error")
      }
    }
}
