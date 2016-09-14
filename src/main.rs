#[macro_use]
extern crate lazy_static;   // lazy static initializers
extern crate lalrpop_util;  // parser generator
extern crate rustyline;     // line editing and ctrl+c handling
extern crate ctrlc;         // we still need ctrl+c handling when not in rustyline
extern crate regex;

pub mod syntax;
pub mod unify;
pub mod solve;
pub mod token;
pub mod lexer;
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
use lexer::Lexer;

use rustyline::Editor;

enum Status<E> {
  Ok,
  Quit,
  Err(E),
}

/* [exec_cmd cmd] executes the toplevel command [cmd].
   Returns Some() when the computation succeeded and None
   when the command failed.
*/
fn exec_cmd(db: &mut Database, cmd: &ToplevelCmd, rl: &mut Editor<()>, interrupted: &Arc<AtomicBool>)
-> Status<Error> {
  match cmd {
    &Assert(ref a) => { assert(db, a.clone());  Status::Ok },
    &Goal(ref g)   => { solve_toplevel(db, &g, rl, interrupted); Status::Ok },
    &Quit          => Status::Quit,
    &Use(ref file) => match exec_file(db, &file, rl, interrupted) {
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
fn exec_file(db: &mut Database, filename: &String, rl: &mut Editor<()>, interrupted: &Arc<AtomicBool>)
-> Status<Error> {
  use std::io::prelude::Read;
  match File::open(filename) {
    Err(e)    => return Status::Err(e),
    Ok(mut f) => {
      let mut s = String::new();
      match f.read_to_string(&mut s) {
        Err(e) => return Status::Err(e),
        Ok(_)  => {
          match parse_Toplevel(&s, Lexer::new(&s)) {
            Ok(cmds) => exec_cmds(db, &cmds, rl, interrupted),
            Err(_)   => { println!("Parse error"); Status::Ok }
          }
        }
      }
    }
  }
}

/* [exec_cmds cmds] executes the list of toplevel commands [cmds]. */
fn exec_cmds(db: &mut Database, cmds: &Vec<ToplevelCmd>, rl: &mut Editor<()>, interrupted: &Arc<AtomicBool>)
-> Status<Error>
{
  let mut ret : Status<Error> = Status::Ok;
  for &ref cmd in cmds.iter() {
    match exec_cmd(db, cmd, rl, interrupted) {
      Status::Quit   => { ret = Status::Quit; break },
      Status::Err(e) => { ret = Status::Err(e); break },
      _              => continue
    }
  }
  ret
}

fn main() {
    use rustyline::error::ReadlineError;

    // This is for handling Ctrl-C. We note the interruption
    // so that we can check for it inside the computations, and
    // abort as requested.
    let interrupted = Arc::new(AtomicBool::new(false));
    let i = interrupted.clone();
    ctrlc::set_handler(move || {
      i.store(true, Ordering::SeqCst);
      println!("Interrupted by user");
    });

    let mut rl = Editor::<()>::new();
    let mut db: Database = vec![];
    /* Load up the standard prelude */
    let prelude_str = include_str!("prelude.pl");
    match parse_Toplevel(&prelude_str, Lexer::new(&prelude_str)) {
      Ok(cmds) => match exec_cmds(&mut db, &cmds, &mut rl, &interrupted) {
          Status::Quit   => panic!("$quit from prelude"),
          Status::Err(_) => panic!("Exiting due to unexpected error in prelude"),
          _              => ()
      },
      _        => panic!("Failed to parse prelude")
    }

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

    let prompt = "Prolog> ";

    loop {
      let readline = rl.readline(&prompt);
      match readline {
        Ok(s) => {
          if s == "" { continue };
          // First add it to the history
          rl.add_history_entry(&s);
          match parse_Toplevel(&s, Lexer::new(&s)) {
            Ok(commands)  => match exec_cmds(&mut db, &commands, &mut rl, &interrupted) {
              Status::Quit   => return,
              Status::Err(e) => {
                println!("Exiting due to unexpected error: {}", e);
                return
              },
              _              => continue
            },
            Err(_)        => println!("Parse error")
          }
        },
        Err(ReadlineError::Interrupted) => {
          println!("Interrupted by user");
        },
        Err(ReadlineError::Eof) => {
          break
        },
        Err(err) => {
          println!("Error: {:?}", err);
          break
        }
      }
    }
}
