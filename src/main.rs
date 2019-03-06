pub mod syntax;
pub mod unify;
pub mod solve;
pub mod token;
pub mod lexer;
pub mod heap;

use std::fs::File;
use std::io::Error;

use std::collections::vec_deque::VecDeque;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use rustyline::Editor;
use lazy_static::lazy_static;

// Option parsing
use std::path::PathBuf;
use structopt::StructOpt;

use directories::{ProjectDirs};

use crate::parser::ToplevelParser;
use crate::solve::{solve_toplevel, assert};
use crate::syntax::Database;
use crate::syntax::ToplevelCmd;
use crate::syntax::ToplevelCmd::*;
use crate::heap::Heap;
use crate::lexer::Lexer;

use lalrpop_util::lalrpop_mod;

lalrpop_mod!(pub parser); // lalrpop generated parser

#[derive(Debug, StructOpt)]
#[structopt(name = "prolog", about = "prolog usage")]
struct Opt {
    /// Activate verbose mode (currently does nothing)
    #[structopt(short = "v", long = "verbose")]
    verbose: bool,
    /// Print usage and quit
    #[structopt(short = "h", long = "help")]
    help: bool,
    /// Optionally read a file on start up
    #[structopt(parse(from_os_str))]
    input: Option<PathBuf>,
}

enum Status<E> {
    Ok,
    Quit,
    Err(E),
}

lazy_static! {
    static ref PARSER: ToplevelParser = ToplevelParser::new();
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
                    match PARSER.parse(heap, &s, Lexer::new(&s)) {
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
        let opt = Opt::from_args();

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
        match PARSER.parse(&mut heap, prelude_str, Lexer::new(prelude_str)) {
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

        if opt.verbose {
            println!("{:?}", opt);
        }

        if let Some(path) = opt.input {
            use std::io::prelude::*;
            let mut file = File::open(path).expect("Unable to open file");
            let mut contents = String::new();
            file.read_to_string(&mut contents).expect("Unable to read file");

            match PARSER.parse(&mut heap, &contents, Lexer::new(&contents)) {
                Ok(cmds) => match exec_cmds(&mut db, &mut heap, &cmds, &mut rl, &interrupted, max_depth) {
                    Status::Quit   => panic!("$quit from user input"),
                    Status::Err(_) => panic!("Exiting due to unexpected error in user input"),
                    _              => ()
                },
                _                => panic!("Failed to parse user input")
            }

        }

        // failure to load history is a silent failure :(
        if let Some(proj_dirs) = ProjectDirs::from("com", "dagit", "rust-prolog") {
            let hist_dir = proj_dirs.cache_dir();
            if let Ok(()) = std::fs::create_dir_all(hist_dir) {
                let mut hist_path = hist_dir.to_path_buf();
                hist_path.push("history");
                match rl.load_history(&hist_path) {
                    Err(_) => (), // :(
                    Ok(()) => (),
                }
            }
        }

        let prompt = "Prolog> ";

        loop {
            let readline = rl.readline(prompt);
            match readline {
                Ok(s) => {
                    if s == "" { continue };
                    // First add it to the history
                    rl.add_history_entry(s.clone());
                    let parse_result = PARSER.parse(&mut heap, &s, Lexer::new(&s));
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
        // failure to save history is a silent failure :(
        if let Some(proj_dirs) = ProjectDirs::from("com", "dagit", "rust-prolog") {
            let hist_dir = proj_dirs.cache_dir();
            if let Ok(()) = std::fs::create_dir_all(hist_dir) {
                let mut hist_path = hist_dir.to_path_buf();
                hist_path.push("history");
                match rl.save_history(&hist_path) {
                    Err(_) => (), // :(
                    Ok(()) => (),
                }
            }
        }
    }).unwrap();
    interpreter.join().unwrap();

}
