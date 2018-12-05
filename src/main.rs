#[macro_use]
extern crate lazy_static;   // lazy static initializers
extern crate lalrpop_util;  // parser generator
extern crate rustyline;     // line editing and ctrl+c handling
extern crate ctrlc;         // we still need ctrl+c handling when not in rustyline
extern crate regex;
#[macro_use]
extern crate gc_derive;
extern crate gc;

pub mod syntax;
pub mod unify;
pub mod solve;
pub mod token;
pub mod lexer;
pub mod heap;
pub mod parser; // lalrpop generated parser

use std::fs::File;
use std::io::Error;

use std::collections::vec_deque::VecDeque;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use parser::parse_Toplevel;

use solve::{solve_toplevel, assert};
use syntax::Database;
use syntax::ToplevelCmd;
use syntax::ToplevelCmd::*;
use heap::Heap;
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
fn exec_cmd(db: &mut Database, heap: &mut Heap, cmd: &ToplevelCmd, rl: &mut Editor<()>, interrupted: &Arc<AtomicBool>, max_depth: i32)
            -> Status<Error> {
    match *cmd {
        Assert(ref a) => { assert(db, heap, a);  Status::Ok },
        Goal(ref g)   => {
            interrupted.store(false, Ordering::SeqCst);
            solve_toplevel(db, heap, g, rl, interrupted, max_depth);
            heap.cleanup();
            Status::Ok
        },
        Quit          => Status::Quit,
        Use(ref file) => match exec_file(db, heap, file, rl, interrupted, max_depth) {
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
fn exec_file(db: &mut Database, heap: &mut Heap, filename: &str, rl: &mut Editor<()>, interrupted: &Arc<AtomicBool>, max_depth: i32)
             -> Status<Error> {
    use std::io::prelude::Read;
    match File::open(filename) {
        Err(e)    => Status::Err(e),
        Ok(mut f) => {
            let mut s = String::new();
            match f.read_to_string(&mut s) {
                Err(e) => Status::Err(e),
                Ok(_)  => {
                    match parse_Toplevel(heap, &s, Lexer::new(&s)) {
                        Ok(cmds) => exec_cmds(db, heap, &cmds, rl, interrupted, max_depth),
                        Err(_)   => { println!("Parse error"); Status::Ok }
                    }
                }
            }
        }
    }
}

/* [exec_cmds cmds] executes the list of toplevel commands [cmds]. */
fn exec_cmds(db: &mut Database, heap: &mut Heap, cmds: &[ToplevelCmd], rl: &mut Editor<()>, interrupted: &Arc<AtomicBool>, max_depth: i32)
             -> Status<Error>
{
    let mut ret : Status<Error> = Status::Ok;
    for cmd in cmds.iter() {
        match exec_cmd(db, heap, cmd, rl, interrupted, max_depth) {
            Status::Quit   => { ret = Status::Quit; break },
            Status::Err(e) => { ret = Status::Err(e); break },
            _              => continue
        }
    }
    ret
}

fn main() {
    use rustyline::error::ReadlineError;
    use std::thread;
    
    /* We create a new thread for the interpreter because that's the
     * simplest way to increase the stack size. Which we need to do
     * because we allocated everything on the stack and the default
     * stack size is pretty small.
     */
    let max_depth = 10_000i32;
    let interpreter = thread::Builder::new().stack_size(128 * 1024 * 1024).spawn(move || {

        // This is for handling Ctrl-C. We note the interruption
        // so that we can check for it inside the computations, and
        // abort as requested.
        let interrupted = Arc::new(AtomicBool::new(false));
        let i = Arc::clone(&interrupted);
        ctrlc::set_handler(move || {
            i.store(true, Ordering::SeqCst);
            println!("Interrupted by ctrl-c");
        }).expect("Error setting Ctrl-C handler");
        
        let mut rl = Editor::<()>::new();
        let mut db: Database = VecDeque::new();
        let mut heap = Heap::new();
        /* Load up the standard prelude */
        let prelude_str = include_str!("prelude.pl");
        match parse_Toplevel(&mut heap, prelude_str, Lexer::new(prelude_str)) {
            Ok(cmds) => match exec_cmds(&mut db, &mut heap, &cmds, &mut rl, &interrupted, max_depth) {
                Status::Quit   => panic!("$quit from prelude"),
                Status::Err(_) => panic!("Exiting due to unexpected error in prelude"),
                _              => ()
            },
            _                => panic!("Failed to parse prelude")
        }

        println!(r#"Welcome to rust-prolog!"#);
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
            let readline = rl.readline(prompt);
            match readline {
                Ok(s) => {
                    if s == "" { continue };
                    // First add it to the history
                    rl.add_history_entry(s.clone());
                    let parse_result = parse_Toplevel(&mut heap, &s, Lexer::new(&s));
                    match parse_result {
                        Ok(commands)  => match exec_cmds(&mut db, &mut heap, &commands, &mut rl, &interrupted, max_depth) {
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
    }).unwrap();
    interpreter.join().unwrap();
}
