/* The prolog solver. */
use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use syntax::{Database, Environment, Clause, Assertion, Term, Atom,
            string_of_env};
use unify::{unify_atoms};
use rustyline::Editor;

/* A value of type [choice] represents a choice point in the proof
search at which we may continue searching for another solution. It
is a tuple [(asrl, enn, c, n)] where [asrl] for other solutions of
clause [c] in environment [env], using assertion list [asrl], where [n]
is the search depth. */
type Choice = (Database, Environment, Clause, i32);

/* The global database of assertions cannot be represented with a
global variable, like in ML */

/* Add a new assertion at the end of the current database. */
pub fn assert(database: &mut Database, a: Assertion) {
    database.push(a);
}

/* Exception [NoSolution] is raised when a goal cannot be proved. */
struct NoSolution;

/* [renumber_term t n] renumbers all variable instances occurring in
term [t] so that they have level [n]. */
fn renumber_term(n: i32, t: &Term) -> Term {
    match *t {
        Term::Var((ref x, _))    => Term::Var((x.clone(),n)),
        Term::Const(ref c)       => Term::Const(c.clone()),
        Term::App(ref c, ref ts) => Term::App(c.clone(),
                                            ts.iter()
                                            .map( |t|
                                                    renumber_term(n, t) )
                                            .collect::<Vec<Term>>())
    }
}

/* [renumber_atom n a] renumbers all variable instances occurring in
atom [a] so that they have level [n]. */
fn renumber_atom(n: i32, &(ref c, ref ts):&Atom) -> Atom {
    (c.clone(), ts.iter()
     .map( |t|
             renumber_term(n, t) )
     .collect::<Vec<Term>>() )
}

/* [display_solution ch env] displays the solution of a goal encoded
by [env]. It then gives the user the option to search for other
solutions, as described by the list of choice points [ch], or to abort
the current proof search. */
fn display_solution(ch: &Vec<Choice>, env: &Environment, rl: &mut Editor<()>, interrupted: &Arc<AtomicBool>)
                    -> Result<(), NoSolution>
{
    /* This is probably the least efficient way to figure out
    when we're done */
    let answer = string_of_env(env);
    if answer == "Yes" {
        Ok(println!("Yes"))
    } else if ch.is_empty() {
        Ok(println!("{}", answer))
    } else {
        println!("{} \n", answer);
        let readline = rl.readline("more? (y/n) [y] ");
        match readline {
            Ok(s) => {
                let input = s.trim();
                if input == "y" || input == "yes" || input == "" {
                    continue_search(ch, rl, interrupted)
                } else {
                    Err(NoSolution)
                }
            },
            _  => { Err(NoSolution) }
        }
    }
}

/* [continue_search ch] looks for other answers. It accepts a list of
choices [ch]. It continues the search at the first choice in the list. */
fn continue_search(ch: &Vec<Choice>, rl: &mut Editor<()>, interrupted: &Arc<AtomicBool>) -> Result<(), NoSolution>
{
    if ch.is_empty() {
        Err(NoSolution)
    } else {
        let mut ch = ch.clone();
        let (asrl, env, gs, n) = ch.pop().expect(concat!(file!(), ":", line!()));
        solve(&ch, &asrl, &env, &gs, n, rl, interrupted)
    }
}

/* [solve ch asrl env c n] looks for the proof of clause [c]. Other
arguments are:

[ch] is a list of choices at which we may look for other solutions,

[asrl] is the list of assertions that are used to reduce [c] to subgoals,

[env] is the current environment (values of variables),

[n] is the search depth, which is increased at each level of search.

When a solution is found, it is printed on the screen. The user
then decides whether other solutions should be searched for.
 */
fn solve(ch:          &Vec<Choice>,
         asrl:        &Database,
         env:         &Environment,
         c:           &Clause,
         n:           i32,
         rl:          &mut Editor<()>,
         interrupted: &Arc<AtomicBool>)
         -> Result<(), NoSolution>
{
    if c.is_empty() {
        /* All atoms are solved, we found a solution */
        display_solution(ch, env, rl, interrupted)
    } else if interrupted.load(Ordering::SeqCst) {
        Err(NoSolution)
    } else {
        /* Reduce the first atom in the clause */
        let mut new_c = c.clone();
        let a = new_c.pop().expect(concat!(file!(), ":", line!()));
        match reduce_atom(env, n, &a, asrl) {
            None =>
            /* This clause cannot be solved, look for other solutions */
                continue_search(ch, rl, interrupted),
            Some((new_asrl, new_env, d)) => {
                /* The atom was reduced to subgoals [d]. Continue
                search with the subgoals added to the list of goals. */
                /* Add a new choice */
                let mut ch = ch.clone();
                ch.push((new_asrl,env.clone(),c.clone(),n));
                let d  = d.into_iter().chain(new_c.into_iter())
                    .collect::<Clause>();
                solve(&ch, asrl, &new_env, &d, n+1, rl, interrupted)
            }
        }
    }
}

/* [reduce_atom a asrl] reduces atom [a] to subgoals by using the
first assertion in the assertion list [asrl] whose conclusion matches
[a]. It returns [None] if the atom cannot be reduced. */
fn reduce_atom(env: &Environment, n: i32, a: &Atom, local_asrl: &Database)
               -> Option<(Database, Environment, Clause)>
{
    if local_asrl.is_empty() {
        None
    } else {
        let mut asrl2 = local_asrl.clone();
        let (b, lst)  = asrl2.pop().expect(concat!(file!(), ":", line!()));
        let try_env = unify_atoms(env, a, &renumber_atom(n, &b));
        match try_env {
            Err(_)       => reduce_atom(env, n, a, &asrl2),
            Ok(new_env)  => Some((asrl2, new_env,
                                 lst.iter()
                                 .map( |l| renumber_atom(n, l))
                                 .collect::<Clause>()))
        }
    }
}

/* [solve_toplevel c] searches for the proof of clause [c] using
the "global" database. This function is called from the main
program */
pub fn solve_toplevel(db: &Database, c: &Clause, rl: &mut Editor<()>, interrupted: &Arc<AtomicBool>) {
    match solve(&vec![], db, &HashMap::new(), c, 1, rl, interrupted) {
        Err(NoSolution) => println!("No"),
        Ok(()) => ()
    }
}
