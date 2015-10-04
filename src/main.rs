extern crate lalrpop_util;  // parser generator
extern crate rl_sys;        // provides readline
extern crate ctrlc;         // Wrapper for handling Ctrl-C

pub mod syntax;
pub mod unify;
pub mod solve;
pub mod parser; // lalrpop generated parser

use std::fs::File;
use std::io::Error;

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;


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
fn exec_cmd(db: &mut Database, cmd: &ToplevelCmd, interrupted: &Arc<AtomicBool>)
-> Status<Error> {
  match cmd {
    &Assert(ref a) => { assert(db, a.clone());               Status::Ok },
    &Goal(ref g)   => { solve_toplevel(db, &g, interrupted); Status::Ok },
    &Quit          => Status::Quit,
    &Use(ref file) => match exec_file(db, &file, interrupted) {
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
fn exec_file(db: &mut Database, filename: &String, interrupted: &Arc<AtomicBool>)
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
            Ok(cmds) => exec_cmds(db, &cmds, interrupted),
            Err(_)   => { println!("Parse error"); Status::Ok }
          }
        }
      }
    }
  }
}

/* [exec_cmds cmds] executes the list of toplevel commands [cmds]. */
fn exec_cmds(db: &mut Database, cmds: &Vec<ToplevelCmd>, interrupted: &Arc<AtomicBool>)
-> Status<Error>
{
  let mut ret : Status<Error> = Status::Ok;
  for &ref cmd in cmds.iter() {
    match exec_cmd(db, cmd, interrupted) {
      Status::Quit   => { ret = Status::Quit; break },
      Status::Err(e) => { ret = Status::Err(e); break },
      _              => continue
    }
  }
  ret
}

fn main() {
    use rl_sys::{readline, add_history};
    use ctrlc::CtrlC;
    // This is for handling Ctrl-C. We note the interruption
    // so that we can check for it inside the computations, and
    // abort as requested.
    let interrupted = Arc::new(AtomicBool::new(false));
    let i = interrupted.clone();
    CtrlC::set_handler(move || {
        i.store(true, Ordering::SeqCst);
        println!("Interrupted by user");
    });

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
      if s == "" { continue };
      // First add it to the history
      add_history(s.clone());
      /* Always reset the state of interrupted before we start processing */
      interrupted.store(false, Ordering::SeqCst);
      match parse_Toplevel(&s) {
        Ok(commands)  => match exec_cmds(&mut db, &commands, &interrupted) {
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
