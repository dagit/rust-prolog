/* The prolog solver. */
use im::HashMap;
use std::collections::vec_deque::VecDeque;
use std::iter::once;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use crate::heap::{Heap, Lifetime};
use crate::syntax::{
    generate_contrapositives, make_complementary, string_of_env, Assertion, Atom, Database,
    Environment, Term,
};
use crate::unify::{unify_atoms, unify_terms};
use rustyline::history::DefaultHistory;
use rustyline::Editor;

/* A value of type [choice] represents a choice point in the proof
search at which we may continue searching for another solution. It
is a tuple [(asrl, enn, c, n)] where [asrl] for other solutions of
clause [c] in environment [env], using assertion list [asrl], where [n]
is the search depth. */
type Choice = (Database, Environment, FramableClause, i32);

/* As part of model elimination, it is useful to track assumptions
 * separately from the rest of the search state. We accomplish this
 * by "framing" atoms. Because this is state specific to the solver
 * these types shouldn't be exposed outside of this module.
 */
#[derive(PartialEq, Copy, Clone, Debug)]
enum FrameStatus {
    Unframed,
    Framed,
}

type FramableAtom = (Atom, FrameStatus);
type FramableClause = VecDeque<FramableAtom>;

/* The global database of assertions cannot be represented with a
global variable, like in ML */

/* Add a new assertion at the end of the current database. */
pub fn assert(database: &mut Database, heap: &mut Heap, a: &Assertion) {
    let mut contrapositives = generate_contrapositives(heap, a, Lifetime::Perm);
    database.append(&mut contrapositives);
}

/* Exception [NoSolution] is raised when a goal cannot be proved. */
enum Error {
    NoSolution,
    DepthExhausted,
}

/* [renumber_term t n] renumbers all variable instances occurring in
term [t] so that they have level [n]. */
fn renumber_term(heap: &mut Heap, n: i32, t: &Term) -> Arc<Term> {
    match *t {
        Term::Var((ref x, _)) => heap.insert_term(Term::Var((x.clone(), n)), Lifetime::Ephemeral),
        Term::Const(ref c) => heap.insert_term(Term::Const(c.clone()), Lifetime::Ephemeral),
        Term::App(ref c, ref ts) => {
            let new_t = Term::App(
                c.clone(),
                ts.iter()
                    .map(|t| renumber_term(heap, n, t))
                    .collect::<Vec<Arc<Term>>>(),
            );
            heap.insert_term(new_t, Lifetime::Ephemeral)
        }
    }
}

/* [renumber_atom n a] renumbers all variable instances occurring in
atom [a] so that they have level [n]. */
fn renumber_atom(heap: &mut Heap, n: i32, (c, ts): &Atom) -> Atom {
    (
        c.clone(),
        ts.iter()
            .map(|t| renumber_term(heap, n, t))
            .collect::<Vec<Arc<Term>>>(),
    )
}

struct Solver<'a> {
    database: &'a Database,
    choices: Vec<Choice>,
    env: Environment,
    heap: &'a mut Heap,
    interrupted: &'a Arc<AtomicBool>,
    rl: &'a mut Editor<(), DefaultHistory>,
    // Maximum depth for the current iteration.
    max_depth: i32,
    // The maximum seen depth in the current iteration.
    // Tracking this allows us to exit iterative deepening when
    // we've visited the entire search space but haven't yet hit
    // the search depth limit.
    cur_depth: i32,
}

impl<'a> Solver<'a> {
    fn new(
        db: &'a Database,
        heap: &'a mut Heap,
        rl: &'a mut Editor<(), DefaultHistory>,
        interrupted: &'a Arc<AtomicBool>,
        max_depth: i32,
    ) -> Self {
        Solver {
            database: db,
            choices: vec![],
            env: HashMap::new(),
            heap,
            interrupted,
            rl,
            max_depth,
            cur_depth: 0,
        }
    }

    /* [display_solution] displays the solution of a goal encoded
    by [env] and the current search depth. It then gives the user the option to search for other
    solutions, as described by the list of choice points, or to abort the current proof search. */
    fn display_solution(&mut self, n: i32) -> Result<(), Error> {
        /* Due to the way iterative deepening works, we only need to print an answer the first time
         * we find it. That is, at the first depth we see it.
         */
        if n < self.max_depth {
            return self.continue_search();
        }
        /* This is probably the least efficient way to figure out
        when we're done */
        let answer = string_of_env(&self.env, self.heap);
        if answer == "Yes" {
            println!("Yes");
            Ok(())
        } else if self.choices.is_empty() {
            println!("{}", answer);
            Ok(())
        } else {
            println!("{} \n", answer);
            let readline = self.rl.readline("more? (y/n) [y] ");
            match readline {
                Ok(s) => {
                    let input = s.trim();
                    if input == "y" || input == "yes" || input.is_empty() {
                        self.continue_search()
                    } else {
                        Err(Error::NoSolution)
                    }
                }
                _ => Err(Error::NoSolution),
            }
        }
    }

    /* [continue_search a] looks for other answers. It uses the choices list of
    choices. It continues the search at the first choice in the list.
    */
    fn continue_search(&mut self) -> Result<(), Error> {
        if self.choices.is_empty() && self.cur_depth < self.max_depth {
            Err(Error::NoSolution)
        } else if self.choices.is_empty() {
            Err(Error::DepthExhausted)
        } else {
            let (asrl, env, gs, n) = self.choices.pop().expect(concat!(file!(), ":", line!()));
            self.env = env;
            self.solve(&asrl, &gs, n)
        }
    }

    /* [solve asrl c n] looks for the proof of clause [c]. Other
    arguments are:

    [asrl] is the list of assertions that are used to reduce [c] to subgoals,

    [n] is the search depth, which is increased at each level of search.

    When a solution is found, it is printed on the screen. The user
    then decides whether other solutions should be searched for.
     */
    fn solve(&mut self, asrl: &Database, c: &FramableClause, n: i32) -> Result<(), Error> {
        // TODO: make these println into debugging diagnostics
        //println!("c = {}", string_of_clauses(c));

        self.cur_depth = std::cmp::max(self.cur_depth, n);
        //First check all of our early exit conditions

        // All atoms are solved, we found a solution
        if c.is_empty() {
            return self.display_solution(n);
        }
        // user requested we abort
        if self.interrupted.load(Ordering::SeqCst) {
            return Err(Error::NoSolution);
        }
        // abort this branch, and backtrack according to iterated deepening search
        if n > self.max_depth {
            return self.continue_search();
        }

        // Now we're ready to do one step of solving the goal
        let mut new_c = c.to_owned();
        // this pop cannot fail because we made sure that c is non-empty
        match new_c.pop_front().unwrap() {
            /* if the left most atom is framed we remove it and call solve with essentially the
             * same state */
            (_a, FrameStatus::Framed) => {
                //println!("removing framed: {}", string_of_clauses(&[(_a,FrameStatus::Framed)]));
                self.solve(asrl, &new_c, n)
            }
            (a, FrameStatus::Unframed) => {
                //println!("a = {}", string_of_clauses(&[(a.to_owned(),FrameStatus::Unframed)]));
                if is_complementary(self.heap, &a, &new_c) {
                    //println!("found complementary: {}", string_of_clauses(&[(a,FrameStatus::Unframed)]));
                    return self.solve(asrl, &new_c, n);
                }
                match reduce_atom(&self.env, self.heap, n, &a, asrl) {
                    None =>
                    /* This clause cannot be solved, look for other solutions */
                    {
                        self.continue_search()
                    }
                    Some((new_asrl, new_env, d)) => {
                        /* The atom was reduced to subgoals [d]. Continue
                        search with the subgoals added to the list of goals. */
                        /* Add a new choice */
                        //let mut ch = self.choices.to_owned();
                        self.choices
                            .push((new_asrl, self.env.clone(), c.to_owned(), n));
                        self.env = new_env;
                        //println!("inserting: {} and {}", string_of_clauses(&new_c), string_of_clauses(&d));
                        let d = d
                            .into_iter()
                            .chain(once((a, FrameStatus::Framed)))
                            .chain(new_c)
                            .collect::<FramableClause>();
                        self.solve(self.database, &d, n + 1)
                    }
                }
            }
        }
    }
}

/* uses unification to search for framed atoms whose complement unifies with the given atom. */
fn is_complementary(heap: &mut Heap, a: &Atom, c: &FramableClause) -> bool {
    // this attemps to find a "complementary" match using unification
    // eg., not(p) is complementary to p (and vice-versa)
    let try_complement = make_complementary(heap, a, Lifetime::Ephemeral);
    if let Some(t) = try_complement {
        //println!("negation, t = {}", string_of_term(&t));
        for x in c {
            if let ((ref c, ref ts), FrameStatus::Framed) = *x {
                let t2 = if ts.is_empty() {
                    heap.insert_term(Term::Const(c.to_owned()), Lifetime::Ephemeral)
                } else {
                    heap.insert_term(Term::App(c.to_owned(), ts.to_owned()), Lifetime::Ephemeral)
                };
                match unify_terms(&HashMap::new(), heap, &t, &t2) {
                    Err(_) => (),
                    Ok(_) => return true,
                }
            }
        }
    }
    false
}

/* [reduce_atom a asrl] reduces atom [a] to subgoals by using the
first assertion in the assertion list [asrl] whose conclusion matches
[a]. It returns [None] if the atom cannot be reduced. */
fn reduce_atom(
    env: &Environment,
    heap: &mut Heap,
    n: i32,
    a: &Atom,
    local_asrl: &Database,
) -> Option<(Database, Environment, FramableClause)> {
    if local_asrl.is_empty() {
        None
    } else {
        let mut asrl2 = local_asrl.to_owned();
        let (b, lst) = asrl2.pop_front().expect(concat!(file!(), ":", line!()));
        let new_b = renumber_atom(heap, n, &b);
        let try_env = unify_atoms(env, heap, a, &new_b);
        match try_env {
            Err(_) => reduce_atom(env, heap, n, a, &asrl2),
            Ok(new_env) => Some((
                asrl2,
                new_env,
                lst.iter()
                    .map(|l| (renumber_atom(heap, n, l), FrameStatus::Unframed))
                    .collect::<FramableClause>(),
            )),
        }
    }
}

/* [solve_toplevel c] searches for the proof of clause [c] using
the "global" database. This function is called from the main
program */
pub fn solve_toplevel(
    db: &Database,
    heap: &mut Heap,
    c: &[Atom],
    rl: &mut Editor<(), DefaultHistory>,
    interrupted: &Arc<AtomicBool>,
    max_depth: i32,
) {
    let mut depth = 0;
    let c = c
        .iter()
        .map(|x| (x.to_owned(), FrameStatus::Unframed))
        .collect::<FramableClause>();
    loop {
        if depth >= max_depth {
            return println!("Search depth exhausted");
        }
        let mut s = Solver::new(db, heap, rl, interrupted, depth);
        match s.solve(db, &c, 1) {
            Err(Error::DepthExhausted) => depth += 1,
            Err(Error::NoSolution) => return println!("No"),
            Ok(()) => return,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::tests::*;
    use proptest::prelude::*;

    /// Collect all variable levels from a term
    fn var_levels(t: &Term) -> Vec<i32> {
        match *t {
            Term::Var((_, n)) => vec![n],
            Term::Const(_) => vec![],
            Term::App(_, ref ts) => ts.iter().flat_map(|t| var_levels(t)).collect(),
        }
    }

    proptest! {
        #[test]
        fn renumber_term_sets_level(t in arb_term(3), n in 0..100i32) {
            let mut heap = Heap::new();
            let result = renumber_term(&mut heap, n, &t);
            let levels = var_levels(&result);
            for level in levels {
                prop_assert_eq!(level, n);
            }
        }
    }

    proptest! {
        #[test]
        fn renumber_term_preserves_structure(t in arb_term(3), n in 0..100i32) {
            let mut heap = Heap::new();
            let result = renumber_term(&mut heap, n, &t);
            // Const stays Const, Var stays Var, App stays App with same arity
            match (&*t, &*result) {
                (Term::Var(_), Term::Var(_)) => (),
                (Term::Const(a), Term::Const(b)) => prop_assert_eq!(a, b),
                (Term::App(c1, ts1), Term::App(c2, ts2)) => {
                    prop_assert_eq!(c1, c2);
                    prop_assert_eq!(ts1.len(), ts2.len());
                }
                _ => prop_assert!(false, "structure changed: {:?} -> {:?}", *t, *result),
            }
        }
    }

    proptest! {
        #[test]
        fn renumber_term_idempotent(t in arb_term(3), n in 0..100i32) {
            let mut heap = Heap::new();
            let once = renumber_term(&mut heap, n, &t);
            let twice = renumber_term(&mut heap, n, &once);
            prop_assert_eq!(&*once, &*twice);
        }
    }

    proptest! {
        #[test]
        fn renumber_atom_preserves_functor(a in arb_atom(2), n in 0..100i32) {
            let mut heap = Heap::new();
            let (functor, args) = &a;
            let (new_functor, new_args) = renumber_atom(&mut heap, n, &a);
            prop_assert_eq!(functor, &new_functor);
            prop_assert_eq!(args.len(), new_args.len());
            // All variables in the result should have level n
            for arg in &new_args {
                for level in var_levels(arg) {
                    prop_assert_eq!(level, n);
                }
            }
        }
    }
}
