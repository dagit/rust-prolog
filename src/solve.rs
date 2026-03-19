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

enum SolveResult {
    Solution(Environment),
    NoSolution,
    DepthExhausted,
}

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

/* The cur_depth field tracks whether we've explored the full search
space at the current depth limit, enabling iterative deepening to
know when to stop. */

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

/// Outcome of iterative deepening search.
enum SearchOutcome {
    /// A solution was found (there may be more via `next()`).
    Solution(Environment),
    /// The entire search space was explored with no solutions.
    NoSolution,
    /// The maximum iterative deepening depth was reached.
    SearchDepthExhausted,
}

/// Iterative-deepening search iterator. Yields solutions on demand,
/// transparently incrementing depth when a level is exhausted.
struct Search<'a> {
    database: &'a Database,
    heap: &'a mut Heap,
    interrupted: &'a Arc<AtomicBool>,
    choices: Vec<Choice>,
    env: Environment,
    goals: FramableClause,
    /// The overall maximum depth limit.
    max_depth: i32,
    /// The current iterative-deepening depth.
    depth: i32,
    /// The deepest level reached in the current depth iteration.
    cur_depth: i32,
    /// Whether we've started solving at the current depth.
    started: bool,
    done: bool,
}

impl<'a> Search<'a> {
    fn new(
        db: &'a Database,
        heap: &'a mut Heap,
        interrupted: &'a Arc<AtomicBool>,
        goals: FramableClause,
        max_depth: i32,
    ) -> Self {
        Search {
            database: db,
            heap,
            interrupted,
            choices: vec![],
            env: HashMap::new(),
            goals,
            max_depth,
            depth: 0,
            cur_depth: 0,
            started: false,
            done: false,
        }
    }

    /// Reset solver state for a new depth iteration.
    fn reset_for_depth(&mut self) {
        self.choices.clear();
        self.env = HashMap::new();
        self.cur_depth = 0;
        self.started = false;
    }

    /* Iterative solver for a single depth level. Replaces the former
    mutually-recursive Solver::solve/continue_search pair. Every former
    recursive call was a tail call, so each maps to updating (asrl, c, n)
    and continuing the loop. Backtracking pops from self.choices. */
    fn solve_step(&mut self, mut asrl: Database, mut c: FramableClause, mut n: i32) -> SolveResult {
        loop {
            self.cur_depth = std::cmp::max(self.cur_depth, n);

            // All atoms are solved, we found a solution
            if c.is_empty() {
                /* Due to the way iterative deepening works, we only need to
                 * yield an answer the first time we find it. That is, at the
                 * first depth we see it. */
                if n < self.depth {
                    // Duplicate at shallower depth — backtrack
                    match self.choices.pop() {
                        Some((ba, env, bc, bn)) => {
                            self.env = env;
                            asrl = ba;
                            c = bc;
                            n = bn;
                            continue;
                        }
                        None if self.cur_depth < self.depth => return SolveResult::NoSolution,
                        None => return SolveResult::DepthExhausted,
                    }
                }
                return SolveResult::Solution(self.env.clone());
            }

            // User requested abort
            if self.interrupted.load(Ordering::SeqCst) {
                return SolveResult::NoSolution;
            }

            // Depth exceeded — backtrack
            if n > self.depth {
                match self.choices.pop() {
                    Some((ba, env, bc, bn)) => {
                        self.env = env;
                        asrl = ba;
                        c = bc;
                        n = bn;
                        continue;
                    }
                    None if self.cur_depth < self.depth => return SolveResult::NoSolution,
                    None => return SolveResult::DepthExhausted,
                }
            }

            // Pop the leftmost atom from the clause
            let (atom, status) = c.pop_front().unwrap();

            match status {
                // Framed atoms are assumptions — skip them
                FrameStatus::Framed => continue,

                FrameStatus::Unframed => {
                    // Check for complementary match among framed atoms
                    if is_complementary(self.heap, &atom, &c) {
                        continue;
                    }

                    match reduce_atom(&self.env, self.heap, n, &atom, &asrl) {
                        None => {
                            // No matching assertion — backtrack
                            match self.choices.pop() {
                                Some((ba, env, bc, bn)) => {
                                    self.env = env;
                                    asrl = ba;
                                    c = bc;
                                    n = bn;
                                    continue;
                                }
                                None if self.cur_depth < self.depth => {
                                    return SolveResult::NoSolution
                                }
                                None => return SolveResult::DepthExhausted,
                            }
                        }
                        Some((new_asrl, new_env, subgoals)) => {
                            // Save choice point. Reconstruct the full clause
                            // (with the atom we just popped) for backtracking.
                            let mut saved_c = c.clone();
                            saved_c.push_front((atom.clone(), FrameStatus::Unframed));
                            self.choices.push((new_asrl, self.env.clone(), saved_c, n));

                            // Set up state for the next iteration
                            self.env = new_env;
                            c = subgoals
                                .into_iter()
                                .chain(once((atom, FrameStatus::Framed)))
                                .chain(c)
                                .collect();
                            asrl = self.database.clone();
                            n += 1;
                        }
                    }
                }
            }
        }
    }

    /// Advance the search by one solution at the current depth level.
    fn solver_next(&mut self) -> SolveResult {
        let (asrl, c, n) = if !self.started {
            self.started = true;
            (self.database.clone(), self.goals.clone(), 1)
        } else {
            match self.choices.pop() {
                Some((asrl, env, c, n)) => {
                    self.env = env;
                    (asrl, c, n)
                }
                None => {
                    return if self.cur_depth < self.depth {
                        SolveResult::NoSolution
                    } else {
                        SolveResult::DepthExhausted
                    };
                }
            }
        };
        self.solve_step(asrl, c, n)
    }

    /// Like `next()` but distinguishes "no more solutions" from
    /// "search depth exhausted".
    fn next_outcome(&mut self) -> SearchOutcome {
        loop {
            if self.done {
                return SearchOutcome::NoSolution;
            }
            match self.solver_next() {
                SolveResult::Solution(env) => return SearchOutcome::Solution(env),
                SolveResult::NoSolution => {
                    self.done = true;
                    return SearchOutcome::NoSolution;
                }
                SolveResult::DepthExhausted => {
                    self.depth += 1;
                    if self.depth >= self.max_depth {
                        self.done = true;
                        return SearchOutcome::SearchDepthExhausted;
                    }
                    self.reset_for_depth();
                }
            }
        }
    }

    /// Whether there are still remaining choice points to explore.
    fn has_more_choices(&self) -> bool {
        !self.choices.is_empty()
    }
}

impl<'a> Iterator for Search<'a> {
    type Item = Environment;

    fn next(&mut self) -> Option<Environment> {
        match self.next_outcome() {
            SearchOutcome::Solution(env) => Some(env),
            SearchOutcome::NoSolution | SearchOutcome::SearchDepthExhausted => None,
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
    let mut remaining = local_asrl.clone();
    while let Some((b, lst)) = remaining.pop_front() {
        let new_b = renumber_atom(heap, n, &b);
        match unify_atoms(env, heap, a, &new_b) {
            Err(_) => continue,
            Ok(new_env) => {
                return Some((
                    remaining,
                    new_env,
                    lst.iter()
                        .map(|l| (renumber_atom(heap, n, l), FrameStatus::Unframed))
                        .collect::<FramableClause>(),
                ));
            }
        }
    }
    None
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
    let goals = c
        .iter()
        .map(|x| (x.to_owned(), FrameStatus::Unframed))
        .collect::<FramableClause>();
    let mut search = Search::new(db, heap, interrupted, goals, max_depth);
    loop {
        match search.next_outcome() {
            SearchOutcome::Solution(env) => {
                let answer = string_of_env(&env, search.heap);
                if answer == "Yes" {
                    println!("Yes");
                    return;
                }
                println!("{}", answer);
                if !search.has_more_choices() {
                    return;
                }
                println!();
                let readline = rl.readline("more? (y/n) [y] ");
                match readline {
                    Ok(s) => {
                        let input = s.trim();
                        if input != "y" && input != "yes" && !input.is_empty() {
                            return;
                        }
                    }
                    _ => return,
                }
            }
            SearchOutcome::NoSolution => {
                println!("No");
                return;
            }
            SearchOutcome::SearchDepthExhausted => {
                println!("Search depth exhausted");
                return;
            }
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

    // Helper to build a simple atom like "human(socrates)"
    fn make_atom(name: &str, args: Vec<Arc<Term>>) -> Atom {
        (Arc::new(name.to_owned()), args)
    }

    fn make_const(heap: &mut Heap, name: &str) -> Arc<Term> {
        heap.insert_term(Term::Const(Arc::new(name.to_owned())), Lifetime::Perm)
    }

    fn make_var(heap: &mut Heap, name: &str, level: i32) -> Arc<Term> {
        heap.insert_term(
            Term::Var((Arc::new(name.to_owned()), level)),
            Lifetime::Perm,
        )
    }

    fn make_interrupted() -> Arc<AtomicBool> {
        Arc::new(AtomicBool::new(false))
    }

    fn make_goals(atoms: Vec<Atom>) -> FramableClause {
        atoms
            .into_iter()
            .map(|a| (a, FrameStatus::Unframed))
            .collect()
    }

    fn make_search<'a>(
        db: &'a Database,
        heap: &'a mut Heap,
        interrupted: &'a Arc<AtomicBool>,
        goals: FramableClause,
    ) -> Search<'a> {
        Search::new(db, heap, interrupted, goals, 100)
    }

    #[test]
    fn solve_simple_fact() {
        // Assert: human(socrates).
        // Query: ?- human(socrates).
        let mut heap = Heap::new();
        let mut db: Database = VecDeque::new();
        let socrates = make_const(&mut heap, "socrates");
        let fact = make_atom("human", vec![socrates.clone()]);
        assert(&mut db, &mut heap, &(fact.clone(), vec![]));

        let interrupted = make_interrupted();
        let solutions: Vec<_> =
            make_search(&db, &mut heap, &interrupted, make_goals(vec![fact])).collect();
        assert_eq!(solutions.len(), 1);
    }

    #[test]
    fn solve_no_match() {
        // Assert: human(socrates).
        // Query: ?- human(plato).
        let mut heap = Heap::new();
        let mut db: Database = VecDeque::new();
        let socrates = make_const(&mut heap, "socrates");
        let plato = make_const(&mut heap, "plato");
        let fact = make_atom("human", vec![socrates]);
        assert(&mut db, &mut heap, &(fact, vec![]));

        let query = make_atom("human", vec![plato]);
        let interrupted = make_interrupted();
        let solutions: Vec<_> =
            make_search(&db, &mut heap, &interrupted, make_goals(vec![query])).collect();
        assert!(solutions.is_empty());
    }

    #[test]
    fn solve_variable_binding() {
        // Assert: human(socrates). human(plato).
        // Query: ?- human(X).
        // Should yield two solutions.
        let mut heap = Heap::new();
        let mut db: Database = VecDeque::new();
        let socrates = make_const(&mut heap, "socrates");
        let plato = make_const(&mut heap, "plato");
        assert(
            &mut db,
            &mut heap,
            &(make_atom("human", vec![socrates]), vec![]),
        );
        assert(
            &mut db,
            &mut heap,
            &(make_atom("human", vec![plato]), vec![]),
        );

        let x = make_var(&mut heap, "X", 0);
        let query = make_atom("human", vec![x]);
        let interrupted = make_interrupted();
        let solutions: Vec<_> =
            make_search(&db, &mut heap, &interrupted, make_goals(vec![query])).collect();
        assert_eq!(solutions.len(), 2);
    }

    #[test]
    fn solve_with_rule() {
        // Assert: human(socrates). mortal(X) :- human(X).
        // Query: ?- mortal(socrates).
        let mut heap = Heap::new();
        let mut db: Database = VecDeque::new();
        let socrates = make_const(&mut heap, "socrates");
        assert(
            &mut db,
            &mut heap,
            &(make_atom("human", vec![socrates.clone()]), vec![]),
        );

        let x = make_var(&mut heap, "X", 0);
        let rule_head = make_atom("mortal", vec![x.clone()]);
        let rule_body = make_atom("human", vec![x]);
        assert(&mut db, &mut heap, &(rule_head, vec![rule_body]));

        let query = make_atom("mortal", vec![socrates]);
        let interrupted = make_interrupted();
        let solutions: Vec<_> =
            make_search(&db, &mut heap, &interrupted, make_goals(vec![query])).collect();
        assert_eq!(solutions.len(), 1);
    }

    #[test]
    fn solve_interrupted() {
        // The solver should yield no results when interrupted
        let mut heap = Heap::new();
        let mut db: Database = VecDeque::new();
        let socrates = make_const(&mut heap, "socrates");
        assert(
            &mut db,
            &mut heap,
            &(make_atom("human", vec![socrates.clone()]), vec![]),
        );

        let query = make_atom("human", vec![socrates]);
        let interrupted = Arc::new(AtomicBool::new(true));
        let mut search = make_search(&db, &mut heap, &interrupted, make_goals(vec![query]));
        assert!(search.next().is_none());
    }

    #[test]
    fn solve_empty_database() {
        // Query against empty database should yield nothing
        let mut heap = Heap::new();
        let db: Database = VecDeque::new();
        let socrates = make_const(&mut heap, "socrates");
        let query = make_atom("human", vec![socrates]);
        let interrupted = make_interrupted();
        let solutions: Vec<_> =
            make_search(&db, &mut heap, &interrupted, make_goals(vec![query])).collect();
        assert!(solutions.is_empty());
    }
}
