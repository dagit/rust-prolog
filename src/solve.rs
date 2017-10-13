/* The prolog solver. */
use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use syntax::{/*Database, DBSlice,*/ Environment, Clause, ClauseSlice, /*Assertion,*/ Term, Atom,
            Constant,
            FrameStatus, string_of_env, /*string_of_term, string_of_clauses,*/ exists};
use unify::{unify_atoms, unify_terms};
use rustyline::Editor;

/* A value of type [choice] represents a choice point in the proof
search at which we may continue searching for another solution. It
is a tuple [(asrl, enn, c, n)] where [asrl] for other solutions of
clause [c] in environment [env], using assertion list [asrl], where [n]
is the search depth. */
type Choice = (Vec<(Atom, Vec<Atom>)>, Environment, Clause, i32);

/* The global database of assertions cannot be represented with a
global variable, like in ML */

/* Add a new assertion at the end of the current database. */
pub fn assert(database: &mut Vec<(Atom, Vec<Atom>)>, a: (Atom, Vec<Atom>)) {
    database.push(a);
}

/* Exception [NoSolution] is raised when a goal cannot be proved. */
enum Error {
    NoSolution,
    DepthExhausted,
}

/* [renumber_term t n] renumbers all variable instances occurring in
term [t] so that they have level [n]. */
fn renumber_term(n: i32, t: &Term) -> Term {
    match *t {
        Term::Var((ref x, _))    => Term::Var((x.clone(),n)),
        Term::Const(ref c)       => Term::Const(c.clone()),
        Term::App(ref c, ref ts) => {
            Term::App(c.clone(),
                      ts.iter()
                        .map( |t| renumber_term(n, t) )
                        .collect::<Vec<Term>>())
        }
    }
}

/* [renumber_atom n a] renumbers all variable instances occurring in
atom [a] so that they have level [n]. */
fn renumber_atom(n: i32, &(ref c, ref ts):&Atom) -> Atom {
    (c.clone(), ts.iter()
     .map( |t| renumber_term(n, t) )
     .collect::<Vec<Term>>() )
}

/* [display_solution ch env] displays the solution of a goal encoded
by [env]. It then gives the user the option to search for other
solutions, as described by the list of choice points [ch], or to abort
the current proof search. */
fn display_solution(ch: &[Choice], env: &Environment, rl: &mut Editor<()>, interrupted: &Arc<AtomicBool>, max_depth: i32)
                    -> Result<(), Error>
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
                    continue_search(ch, None, rl, interrupted, max_depth)
                } else {
                    Err(Error::NoSolution)
                }
            },
            _  => { Err(Error::NoSolution) }
        }
    }
}

/* [continue_search ch] looks for other answers. It accepts a list of
choices [ch]. It continues the search at the first choice in the list. */
fn continue_search(ch: &[Choice], a: Option<Atom>, rl: &mut Editor<()>, interrupted: &Arc<AtomicBool>, max_depth: i32) -> Result<(), Error>
{
    if ch.is_empty() {
        Err(Error::NoSolution)
    } else {
        let mut ch = ch.to_owned();
        let (asrl, env, mut gs, n) = ch.pop().expect(concat!(file!(), ":", line!()));
        match a {
            None    => solve(&ch, &asrl, &env, &gs, n, rl, interrupted, max_depth),
            Some(a) => {
                gs.push((a,FrameStatus::Framed));
                solve(&ch, &asrl, &env, &gs, n, rl, interrupted, max_depth)
            }
        }
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
fn solve(ch:          &[Choice],
         asrl:        &[(Atom, Vec<Atom>)],
         env:         &Environment,
         c:           &ClauseSlice,
         n:           i32,
         rl:          &mut Editor<()>,
         interrupted: &Arc<AtomicBool>,
         max_depth:   i32)
         -> Result<(), Error>
{
    // TODO: make these println into debugging diagnostics
    //println!("c = {}", string_of_clauses(c));

    //First check all of our early exit conditions

    // All atoms are solved, we found a solution
    if c.is_empty() { return display_solution(ch, env, rl, interrupted, max_depth) }
    // user requested we abort
    if interrupted.load(Ordering::SeqCst) { return Err(Error::NoSolution) }
    // abort according to iterated deepening search
    if n >= max_depth { return Err(Error::DepthExhausted) }

    // Now we're ready to do one step of solving the goal
    let mut new_c = c.to_owned();
    // this pop cannot fail because we made sure that c is non-empty
    match new_c.pop().unwrap() {
        /* if the left most atom is framed we remove it and call solve with essentially the
         * same state */
        (_a, FrameStatus::Framed)  => {
            //println!("removing framed: {}", string_of_clauses(&[(_a,FrameStatus::Framed)]));
            solve(ch, asrl, env, &new_c, n, rl, interrupted, max_depth)
        },
        (a, FrameStatus::Unframed) => {
            //println!("a = {}", string_of_clauses(&[(a.to_owned(),FrameStatus::Unframed)]));
            if is_complementary(&a, &new_c) {
                //println!("found complementary: {}", string_of_clauses(&[(a,FrameStatus::Unframed)]));
                return solve(ch, asrl, env, &new_c, n, rl, interrupted, max_depth)
            }
            match reduce_atom(env, n, &a, asrl) {
                None =>
                /* This clause cannot be solved, look for other solutions */
                    continue_search(ch, Some(a), rl, interrupted, max_depth),
                Some((new_asrl, new_env, d)) => {
                    /* The atom was reduced to subgoals [d]. Continue
                    search with the subgoals added to the list of goals. */
                    /* Add a new choice */
                    let mut ch = ch.to_owned();
                    ch.push((new_asrl,env.clone(),c.to_owned(),n));
                    new_c.push((a,FrameStatus::Framed));
                    //println!("inserting: {} and {}", string_of_clauses(&new_c), string_of_clauses(&d));
                    let d = new_c.into_iter()
                             .chain(d.into_iter())
                             .collect::<Clause>();
                    solve(&ch, asrl, &new_env, &d, n+1, rl, interrupted, max_depth)
                }
            }
        }
    }
}

fn is_complementary(a: &(Constant, Vec<Term>), c: &ClauseSlice) -> bool
{
    // this attemps to find a "complementary" match using unification
    // eg., not(p) is complementary to p (and vice-versa)
    if let Some(t) = make_complementary(a) {
        //println!("negation, t = {}", string_of_term(&t));
        return exists(|x| match *x {
            ((ref c, ref ts), FrameStatus::Framed) => {
                let t2 = if ts.is_empty() {
                    Term::Const(c.to_owned())
                } else {
                    Term::App(c.to_owned(), ts.to_owned())
                };
                //println!("attempting unification of: {:?}, {:?}", t, t2);
                match unify_terms(&HashMap::new(), &t, &t2) {
                    Err(_) => false,
                    Ok(_)  => true,
                }
            },
            _ => false,
            }, c)
    }
    false
}

fn make_complementary(t: &Atom) -> Option<Term>
{
    match *t {
        // this case bakes in double negation elimnation, so that
        // not(p(X1,...,Xn)) =>
        // not(not(p(X1,...,Xn))) =>
        // p(X1,...,Xn)
        (ref c, ref ts) if *c == "not" => {
            // 'not()' should take exactly 1 argument. If not, then
            // this code doesn't know how to construct the complement
            match ts.len() {
                1 => Some(ts.first().unwrap().to_owned()),
                _ => None
            }
        },
        _ => None
    }
}

/* [reduce_atom a asrl] reduces atom [a] to subgoals by using the
first assertion in the assertion list [asrl] whose conclusion matches
[a]. It returns [None] if the atom cannot be reduced. */
fn reduce_atom(env: &Environment, n: i32, a: &Atom, local_asrl: &[(Atom, Vec<Atom>)])
               -> Option<(Vec<(Atom, Vec<Atom>)>, Environment, Clause)>
{
    if local_asrl.is_empty() {
        None
    } else {
        let mut asrl2    = local_asrl.to_owned();
        let (b, lst)     = asrl2.pop().expect(concat!(file!(), ":", line!()));
        let try_env      = unify_atoms(env, a, &renumber_atom(n, &b));
        match try_env {
            Err(_)       => reduce_atom(env, n, a, &asrl2),
            Ok(new_env)  => Some((
                    asrl2,
                    new_env,
                    lst.iter()
                       .map( |l| (renumber_atom(n, l), FrameStatus::Unframed))
                       .collect::<Clause>()
                ))
        }
    }
}

/* [solve_toplevel c] searches for the proof of clause [c] using
the "global" database. This function is called from the main
program */
pub fn solve_toplevel(db: &[(Atom, Vec<Atom>)], c: &[Atom], rl: &mut Editor<()>, interrupted: &Arc<AtomicBool>, max_depth: i32) {
    let mut depth = 0;
    let c = c.iter()
             .map(|x| (x.to_owned(),FrameStatus::Unframed))
             .collect::<Clause>();
    loop {
        if depth >= max_depth { return println!("Search depth exhausted") }
        match solve(&[], db, &HashMap::new(), &c, 1, rl, interrupted, depth) {
            Err(Error::DepthExhausted) => depth += 1,
            Err(Error::NoSolution)     => return println!("No"),
            Ok(())                     => return ()
        }
    }
}
