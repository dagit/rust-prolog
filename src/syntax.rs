/* This is a rust translation of miniprolog from the plzoo:
 * http://andrej.com/plzoo/html/miniprolog.html
 */
/* Abstract syntax */

use im::HashMap;
use std::collections::vec_deque::VecDeque;
use std::iter::once;
use std::sync::Arc;

use crate::heap::{Heap, Lifetime};

/* Constants and atoms are strings starting with lower-case letters. */
pub type Constant = Arc<String>;

/* Variables are strings starting with upper-case letters, followed by
a number which indicates an instance of the variable. Thus a
variable instance is a pair [(x,n)] where [x] is a variable and [n] is an
integer. When the proof search depth is [n] all variables that we need to use
are renamed from [(x,0)] to [(x,n)]. This is necessary so that we do not use
the same variable name in two different applications of the same assertion. */
pub type Variable = (Arc<String>, i32);

/* The datatype of terms */
#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub enum Term {
    Var(Variable),                 // Variable `X1`, `Y0`, `Z2`, ...
    Const(Constant),               // Constant `a`, `b`, `c`, ...
    App(Constant, Vec<Arc<Term>>), // Compound term `f(t_1, ..., t_n)`
}

/* Atomic proposition [p(t_1, ..., t_n)] */
pub type Atom = (Constant, Vec<Arc<Term>>);

/* A conjunction of atomic propositions [p_1, ..., p_n]. The empty
list represens [true]. */
pub type Clause = Vec<Atom>;
pub type ClauseSlice = [Atom];

/* An assertion [(a,b_1,...,b_n)] is a Horn formula
[b_1 & ... & b_n => a]. */
pub type Assertion = (Atom, Clause);

/* An environment is a list of pairs [(x, e)] where [x] is a variable
instance and [e] is a term. An environment represents the current values
of variables. */
pub type Environment = HashMap<Variable, Arc<Term>>;

/* A database is a list of assertions. It represents the current program. */
pub type Database = VecDeque<Assertion>;

/* Toplevel commands */
#[derive(PartialEq, Clone)]
pub enum ToplevelCmd {
    Assert(Assertion), /* Assertion [a :- b_1, ..., b_n.] or [a.] */
    Goal(Clause),      /* Query [?- a] */
    Quit,              /* The [$quit] command. */
    Use(String),       /* The [$use "filename"] command. */
}

static NOT: &str = "not";

/* [lookup env x] returns the value of variable instance [x] in
environment [env]. It returns [Var x] if the variable does not
occur in [env]. */
fn lookup(env: &Environment, heap: &mut Heap, x: &Variable) -> Arc<Term> {
    match env.get(x) {
        Some(y) => y.clone(),
        None => heap.insert_term(Term::Var(x.clone()), Lifetime::Ephemeral),
    }
}

/* [subst_term sub t] substitutes in term [t] values for variables,
as specified by the associative list [s]. It substitutes
repeatedly until the terms stop changing, so this is not the
usual kind of substitution. It is what we need during unification */
pub fn subst_term(env: &Environment, heap: &mut Heap, t: &Term) -> Arc<Term> {
    match *t {
        Term::Var(ref x) => {
            let new_t = lookup(env, heap, x);
            if *t == *new_t {
                new_t
            } else {
                subst_term(env, heap, &new_t)
            }
        }
        Term::Const(_) => heap.insert_term(t.clone(), Lifetime::Ephemeral),
        Term::App(ref c, ref ls) => {
            let mut new_ls = Vec::with_capacity(ls.len());
            for l in ls.iter() {
                new_ls.push(subst_term(env, heap, l));
            }
            heap.insert_term(Term::App(c.clone(), new_ls), Lifetime::Ephemeral)
        }
    }
}

/* [string_of_term t] converts term [t] to its string representation. */
pub fn string_of_term(t: &Term) -> String {
    match *t {
        Term::Var((ref v, 0)) => v.to_string(),
        Term::Var((ref v, n)) => v.to_string() + &n.to_string(),
        Term::Const(ref c) => string_of_const(c),
        Term::App(..) => string_of_app(t),
    }
}

fn string_of_const(t: &str) -> String {
    match t {
        "zero" => "0",
        "nil" => "[]",
        _ => t,
    }
    .to_string()
}

fn string_of_app(t: &Term) -> String {
    match *t {
        Term::App(ref f, ref args) => match (**f).as_str() {
            "cons" => {
                let list_str: Vec<String> = list_map(t, &string_of_term);
                "[".to_string() + &list_str.join(", ") + "]"
            }
            "succ" => nat_to_word(t).to_string(),
            _ => {
                let list_str = string_of_list(args);
                f.to_string() + "(" + &list_str + ")"
            }
        },
        _ => panic!(),
    }
}

fn list_map<A>(list: &Term, f: &dyn Fn(&Term) -> A) -> Vec<A> {
    match *list {
        Term::App(ref t, ref elts) => match (**t).as_str() {
            "cons" => {
                if elts.len() == 2 {
                    let head = &elts[0];
                    let tail = &elts[1];
                    let mut r = vec![f(head)];
                    let ts = list_map(tail, f);
                    r.extend::<Vec<A>>(ts);
                    r
                } else if elts.len() == 1 {
                    let head = &elts[0];
                    vec![f(head)]
                } else {
                    vec![]
                }
            }
            _ => vec![],
        },
        _ => vec![],
    }
}

fn nat_to_word(list: &Term) -> u64 {
    match *list {
        Term::Const(ref t) => match (**t).as_str() {
            "zero" => 0,
            _ => 0,
        },
        Term::App(ref t, ref elts) => match (**t).as_str() {
            "succ" => {
                if elts.len() == 1 {
                    let arg = &elts[0];
                    let acc = nat_to_word(arg);
                    1 + acc
                } else {
                    1
                }
            }
            _ => 0,
        },
        _ => 0,
    }
}

fn string_of_list(args: &[Arc<Term>]) -> String {
    let mut strings = Vec::with_capacity(args.len());
    for l in args.iter() {
        strings.push(string_of_term(l));
    }
    strings.join(", ")
}

/* [string_of_env env] converts environment [env] to its string
representation. It only keeps instance variables at level 0, i.e.,
those that appear in the toplevel goal. */
pub fn string_of_env(env: &Environment, heap: &mut Heap) -> String {
    let toplevels = env
        .iter()
        .filter(|&(&(_, n), _)| n == 0)
        /* This creates copies and is unnecessary */
        .map(|((x, y), z)| ((x.clone(), *y), z.clone()))
        .collect::<Environment>();
    if toplevels.is_empty() {
        "Yes".to_string()
    } else {
        let res = toplevels
            .iter()
            .map(|((x, _), e)| x.to_string() + " = " + &string_of_term(&subst_term(env, heap, e)))
            .collect::<Vec<String>>();
        res.join("\n")
    }
}

/* [exists fn ls] returns [true] if [fn] returns true on at least
one element of [ls], and returns [false] otherwise.
This was added to mimic the standard ML List.exists function. */
pub fn exists<P, A>(predicate: P, ls: &[A]) -> bool
where
    P: Fn(&A) -> bool,
{
    for x in ls.iter() {
        if predicate(x) {
            return true;
        }
    }
    false
}

/* [occurs x t] returns [true] when variable instance [x] appears in
term [t]. */
pub fn occurs(x: &Variable, t: &Term) -> bool {
    match *t {
        Term::Var(ref y) => x == y,
        Term::Const(_) => false,
        Term::App(_, ref ts) => exists(|t| occurs(x, t), ts),
    }
}

// Look through the user's inference rule [a :- b1, ..., bn] and
// compute all the contrapositives of the rule:
// not(b1) :- not(a), b2, ..., bn
// not(b2) :- not(a), b1, b3, ..., bn
// ...
// not(bn) :- not(a), b1, ..., b(n-1)
// For convenience, we also include the original rule.
pub fn generate_contrapositives(heap: &mut Heap, a: &(Atom, Vec<Atom>), lt: Lifetime) -> Database {
    fn term_to_atom(t: &Term) -> Option<Atom> {
        match *t {
            // because we are processing inference rules, this case shouldn't come up. For example,
            // this is a parse error:
            // p :- X.
            Term::Var(_) => None,
            Term::Const(ref c) => Some((c.to_owned(), vec![])),
            Term::App(ref c, ref ts) => Some((c.to_owned(), ts.to_owned())),
        }
    }

    let mut ret: Database = once(a.to_owned()).collect();

    match make_complementary(heap, &a.0, lt) {
        None => (),
        Some(not_head) => {
            for (idx, t) in a.1.iter().enumerate() {
                match make_complementary(heap, t, lt) {
                    None => (),
                    Some(not_t) => {
                        if let (Some(not_head), Some(not_t)) =
                            (term_to_atom(&not_head), term_to_atom(&not_t))
                        {
                            let mut new_tail: Vec<Atom> = a.1.to_owned();
                            new_tail.remove(idx);
                            new_tail.insert(0, not_head);
                            let new_rule = (not_t, new_tail);
                            ret.push_back(new_rule);
                        }
                    }
                }
            }
        }
    }
    ret
}

// Compute the complementary term for an atom. We assume the arity of `not`
// is exactly 1 and fail to produce a term if it is used at any other arity.
//
// Note: this also applies double negation elimination (eg., not(not(p)) = p).
//
pub fn make_complementary(heap: &mut Heap, t: &Atom, lt: Lifetime) -> Option<Arc<Term>> {
    match *t {
        // this case bakes in double negation elimnation, so that
        // not(p(X1,...,Xn)) =>
        // not(not(p(X1,...,Xn))) =>
        // p(X1,...,Xn)
        (ref c, ref ts) if **c == NOT => {
            // 'not()' should take exactly 1 argument. If not, then
            // this code doesn't know how to construct the complement
            match ts.len() {
                1 => Some(ts.first().unwrap().to_owned()),
                _ => None,
            }
        }
        // the `not` introduction case
        (ref c, ref ts) => match ts.len() {
            0 => {
                let tail = heap.insert_term(Term::Const(c.to_owned()), lt);
                let not = heap.insert_string(NOT.to_string(), Lifetime::Perm);
                Some(heap.insert_term(Term::App(not, vec![tail]), lt))
            }
            _ => {
                let tail = heap.insert_term(Term::App(c.to_owned(), ts.to_owned()), lt);
                let not = heap.insert_string(NOT.to_string(), Lifetime::Perm);
                Some(heap.insert_term(Term::App(not, vec![tail]), lt))
            }
        },
    }
}

pub fn str_to_nat(heap: &mut Heap, input: &str, lt: Lifetime) -> Arc<Term> {
    let value: u64 = input.parse::<u64>().unwrap();
    let zero = heap.insert_string("zero".to_string(), Lifetime::Perm);
    let succ = heap.insert_string("succ".to_string(), Lifetime::Perm);
    let mut t = heap.insert_term(Term::Const(zero), Lifetime::Perm);
    for _ in 0..value {
        t = heap.insert_term(Term::App(succ.clone(), vec![t]), lt);
    }
    t
}

pub fn vec_to_list(heap: &mut Heap, elts: Vec<Arc<Term>>, lt: Lifetime) -> Arc<Term> {
    let nil_str = heap.insert_string("nil".to_string(), Lifetime::Perm);
    let nil = heap.insert_term(Term::Const(nil_str), Lifetime::Perm);
    let cons = heap.insert_string("cons".to_string(), Lifetime::Perm);
    let mut t = nil;
    for e in elts.iter().rev() {
        t = heap.insert_term(Term::App(cons.clone(), vec![e.to_owned(), t]), lt);
    }
    t
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use proptest::prelude::*;

    pub fn arb_variable() -> impl Strategy<Value = Variable> {
        ("[A-Z]", 0..5i32).prop_map(|(s, n)| (Arc::new(s), n))
    }

    pub fn arb_constant() -> impl Strategy<Value = Constant> {
        "[a-z]".prop_map(Arc::new)
    }

    pub fn arb_term(depth: u32) -> impl Strategy<Value = Arc<Term>> {
        if depth == 0 {
            prop_oneof![
                arb_variable().prop_map(|v| Arc::new(Term::Var(v))),
                arb_constant().prop_map(|c| Arc::new(Term::Const(c))),
            ]
            .boxed()
        } else {
            prop_oneof![
                arb_variable().prop_map(|v| Arc::new(Term::Var(v))),
                arb_constant().prop_map(|c| Arc::new(Term::Const(c))),
                (
                    arb_constant(),
                    proptest::collection::vec(arb_term(depth - 1), 1..4)
                )
                    .prop_map(|(c, ts)| Arc::new(Term::App(c, ts))),
            ]
            .boxed()
        }
    }

    pub fn arb_atom(depth: u32) -> impl Strategy<Value = Atom> {
        (
            arb_constant(),
            proptest::collection::vec(arb_term(depth), 0..4),
        )
    }

    proptest! {
        #[test]
        fn occurs_reflexive(x in arb_variable()) {
            prop_assert!(occurs(&x, &Term::Var(x.clone())));
        }
    }

    proptest! {
        #[test]
        fn occurs_not_in_const(x in arb_variable(), c in arb_constant()) {
            prop_assert!(!occurs(&x, &Term::Const(c)));
        }
    }

    proptest! {
        #[test]
        fn subst_term_idempotent(t in arb_term(3)) {
            let mut heap = Heap::new();
            let env = HashMap::new();
            let once = subst_term(&env, &mut heap, &t);
            let twice = subst_term(&env, &mut heap, &once);
            prop_assert_eq!(once, twice);
        }
    }

    proptest! {
        #[test]
        fn subst_term_identity_empty_env(t in arb_term(3)) {
            let mut heap = Heap::new();
            let env = HashMap::new();
            let result = subst_term(&env, &mut heap, &t);
            prop_assert_eq!(&*result, &*t);
        }
    }

    proptest! {
        #[test]
        fn make_complementary_double_negation(a in arb_atom(2)) {
            let mut heap = Heap::new();
            let comp1 = make_complementary(&mut heap, &a, Lifetime::Ephemeral);
            prop_assert!(comp1.is_some());
            let comp1 = comp1.unwrap();
            // Convert the term back to an atom to complement again
            let atom2 = match &*comp1 {
                Term::Const(c) => (c.clone(), vec![]),
                Term::App(c, ts) => (c.clone(), ts.clone()),
                Term::Var(_) => return Ok(()), // skip, shouldn't happen
            };
            let comp2 = make_complementary(&mut heap, &atom2, Lifetime::Ephemeral);
            prop_assert!(comp2.is_some());
            // The double complement should match the original atom as a term
            let comp2 = comp2.unwrap();
            let original_as_term = if a.1.is_empty() {
                heap.insert_term(Term::Const(a.0.clone()), Lifetime::Ephemeral)
            } else {
                heap.insert_term(Term::App(a.0.clone(), a.1.clone()), Lifetime::Ephemeral)
            };
            prop_assert_eq!(&*comp2, &*original_as_term);
        }
    }

    proptest! {
        #[test]
        fn str_to_nat_round_trip(n in 0u64..100) {
            let mut heap = Heap::new();
            let term = str_to_nat(&mut heap, &n.to_string(), Lifetime::Ephemeral);
            let result = nat_to_word(&term);
            prop_assert_eq!(result, n);
        }
    }

    proptest! {
        #[test]
        fn vec_to_list_preserves_length(
            elts in proptest::collection::vec(arb_term(1), 0..6)
        ) {
            let mut heap = Heap::new();
            let list = vec_to_list(&mut heap, elts.clone(), Lifetime::Ephemeral);
            let mapped: Vec<String> = list_map(&list, &string_of_term);
            prop_assert_eq!(mapped.len(), elts.len());
        }
    }

    proptest! {
        #[test]
        fn string_of_term_deterministic(t in arb_term(3)) {
            let s1 = string_of_term(&t);
            let s2 = string_of_term(&t);
            prop_assert_eq!(s1, s2);
        }
    }

    proptest! {
        #[test]
        fn generate_contrapositives_includes_original(a in arb_atom(2)) {
            let mut heap = Heap::new();
            let body: Vec<Atom> = vec![];
            let assertion = (a.clone(), body);
            let result = generate_contrapositives(&mut heap, &assertion, Lifetime::Ephemeral);
            // Original rule is always the first entry
            prop_assert!(!result.is_empty());
            let (head, _) = result.front().unwrap();
            prop_assert_eq!(head, &a);
        }
    }

    proptest! {
        #[test]
        fn generate_contrapositives_count(
            head in arb_atom(1),
            body in proptest::collection::vec(arb_atom(1), 1..4),
        ) {
            let mut heap = Heap::new();
            let n = body.len();
            let assertion = (head, body);
            let result = generate_contrapositives(&mut heap, &assertion, Lifetime::Ephemeral);
            // 1 original + n contrapositives (one per body atom)
            prop_assert_eq!(result.len(), 1 + n);
        }
    }

    #[test]
    fn string_of_env_empty_is_yes() {
        let mut heap = Heap::new();
        let env = HashMap::new();
        assert_eq!(string_of_env(&env, &mut heap), "Yes");
    }
}
