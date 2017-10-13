/* This is a rust translation of miniprolog from the plzoo:
 * http://andrej.com/plzoo/html/miniprolog.html
 */
/* Abstract syntax */

use std::collections::HashMap;

/* Constants and atoms are strings starting with lower-case letters. */
pub type Constant = String;

/* Variables are strings starting with upper-case letters, followed by
a number which indicates an instance of the variable. Thus a
variable instance is a pair [(x,n)] where [x] is a variable and [n] is an
integer. When the proof search depth is [n] all variables that we need to use
are renamed from [(x,0)] to [(x,n)]. This is necessary so that we do not use
the same variable name in two different applications of the same assertion. */
pub type Variable = (String, i32);

/* The datatype of terms */
#[derive(PartialEq, Clone, Debug)]
pub enum Term {
    Var(Variable),            /* Variable [X1], [Y0], [Z2], ... */
    Const(Constant),          /* Constant [a], [b], [c], ...    */
    App(Constant, Vec<Term>)  /* Compound term [f(t_1,...,t_n)] */
}

/* Atomic proposition [p(t_1, ..., t_n)] */
pub type Atom = (Constant, Vec<Term>);

/* A conjunction of atomic propositions [p_1, ..., p_n]. The empty
list represens [true]. */
pub type Clause              = Vec<Atom>;
pub type ClauseSlice         = [Atom];

/* An assertion [(a,b_1,...,b_n)] is a Horn formula
[b_1 & ... & b_n => a]. */
pub type Assertion = (Atom, Clause);

/* An environment is a list of pairs [(x, e)] where [x] is a variable
instance and [e] is a term. An environment represents the current values
of variables. */
pub type Environment = HashMap<Variable, Term>;

/* A database is a list of assertions. It represents the current program. */
pub type Database = Vec<Assertion>;
pub type DBSlice  = [Assertion];

#[derive(PartialEq, Copy, Clone, Debug)]
pub enum FrameStatus {
    Unframed,
    Framed,
}

pub type FramableAtom        = (Atom, FrameStatus);
pub type FramableClause      = Vec<FramableAtom>;
pub type FramableClauseSlice = [FramableAtom];

/* Toplevel commands */
#[derive(PartialEq, Clone)]
pub enum ToplevelCmd {
    Assert(Assertion), /* Assertion [a :- b_1, ..., b_n.] or [a.] */
    Goal(Clause),      /* Query [?- a] */
    Quit,              /* The [$quit] command. */
    Use(String)        /* The [$use "filename"] command. */
}

static NOT: &'static str = "not";

/* [lookup env x] returns the value of variable instance [x] in
environment [env]. It returns [Var x] if the variable does not
occur in [env]. */
fn lookup(env: &Environment, x: &Variable) -> Term {
    match env.get(x) {
        Some(y) => y.clone(),
        None    => Term::Var(x.clone())
    }
}

/* [subst_term sub t] substitutes in term [t] values for variables,
as specified by the associative list [s]. It substitutes
repeatedly until the terms stop changing, so this is not the
usual kind of substitution. It is what we need during unification */
pub fn subst_term(env: &Environment, t: &Term) -> Term {
    match *t {
        Term::Var(ref x) => {
            let new_t = lookup(env, x);
            if *t == new_t {
                new_t
            } else {
                subst_term(env, &new_t)
            }
        },
        Term::Const(_) => t.clone(),
        Term::App(ref c, ref ls) => {
            let mut new_ls = Vec::with_capacity(ls.len());
            for l in ls.iter() {
                new_ls.push(subst_term(env, l));
            }
            Term::App(c.clone(), new_ls)
        }
    }
}

/* [string_of_term t] converts term [t] to its string representation. */
pub fn string_of_term(t: &Term) -> String {
    match *t {
        Term::Var((ref v, 0)) => v.clone(),
        Term::Var((ref v, n)) => v.clone() + &n.to_string(),
        Term::Const(ref c) => c.clone(),
        Term::App(ref f, ref ls) => {
            let mut strings = Vec::with_capacity(ls.len());
            for l in ls.iter() {
                strings.push(string_of_term(l));
            }
            if !strings.is_empty() {
                f.clone() + "(" + &strings.join(", ") + ")"
            } else {
                f.clone()
            }
        }
    }
}

pub fn string_of_clauses(cs: &FramableClauseSlice) -> String {
    let mut strings = Vec::with_capacity(cs.len());
    for c in cs {
        match c.to_owned() {
            ((a,ts), FrameStatus::Unframed) => strings.push(string_of_term(&Term::App(a,ts))),
            ((a,ts), FrameStatus::Framed)   => strings.push(format!("[{}]", string_of_term(&Term::App(a,ts)))),
        }
    }
    strings.join(", ")
}

/* [string_of_env env] converts environment [env] to its string
representation. It only keeps instance variables at level 0, i.e.,
those that appear in the toplevel goal. */
pub fn string_of_env(env: &Environment) -> String {
    let toplevels = env.iter()
        .filter( |&(&(_,n),_) | n==0)
    /* This creates copies and is unnecessary */
        .map( |(&(ref x,ref y), z)|
                  ((x.clone(),*y),z.clone()) )
        .collect::<Environment>();
    if toplevels.is_empty() {
        "Yes".to_string()
    } else {
        let res = toplevels.iter()
            .map( |(&(ref x, _), e)|
                      x.clone() + " = " +
                      &string_of_term(&subst_term(env,e)))
            .collect::<Vec<String>>();
        res.join("\n")
    }
}

/* [exists fn ls] returns [true] if [fn] returns true on at least
one element of [ls], and returns [false] otherwise.
This was added to mimic the standard ML List.exists function. */
pub fn exists<P, A>(predicate: P, ls: &[A]) -> bool
    where P: Fn(&A) -> bool {
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
        Term::Var(ref y)     => x == y,
        Term::Const(_)       => false,
        Term::App(_, ref ts) => exists(|t| occurs(x, t), ts)
    }
}

// Look through the user's inference rule [a :- b1, ..., bn] and
// compute all the contrapositives of the rule:
// not(b1) :- not(a), b2, ..., bn
// not(b2) :- not(a), b1, b3, ..., bn
// ...
// not(bn) :- not(a), b1, ..., b(n-1)
// For convenience, we also include the original rule.
pub fn generate_contrapositives(a: &(Atom, Vec<Atom>)) -> Vec<(Atom, Vec<Atom>)>
{
    fn term_to_atom(t: &Term) -> Option<Atom> {
        match *t {
            // because we are processing inference rules, this case shouldn't come up. For example,
            // this is a parse error:
            // p :- X.
            Term::Var(_)             => None,
            Term::Const(ref c)       => Some((c.to_owned(),vec![])),
            Term::App(ref c, ref ts) => Some((c.to_owned(),ts.to_owned())),
        }
    }

    let mut ret = vec![a.to_owned()];

    match make_complementary(&a.0) {
        None           => (),
        Some(not_head) => {
            for (idx, t) in a.1.iter().enumerate() {
                match make_complementary(t) {
                    None        => (),
                    Some(not_t) => {
                        if let (Some(not_head), Some(not_t)) = (term_to_atom(&not_head), term_to_atom(&not_t)) {
                                let mut new_tail: Vec<Atom> = a.1.to_owned();
                                new_tail.remove(idx);
                                new_tail.insert(0, not_head);
                                let new_rule = (not_t, new_tail);
                                ret.push(new_rule);
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
pub fn make_complementary(t: &Atom) -> Option<Term>
{
    match *t {
        // this case bakes in double negation elimnation, so that
        // not(p(X1,...,Xn)) =>
        // not(not(p(X1,...,Xn))) =>
        // p(X1,...,Xn)
        (ref c, ref ts) if *c == NOT => {
            // 'not()' should take exactly 1 argument. If not, then
            // this code doesn't know how to construct the complement
            match ts.len() {
                1 => Some(ts.first().unwrap().to_owned()),
                _ => None
            }
        },
        // the `not` introduction case
        (ref c, ref ts) => {
            match ts.len() {
                0 => Some(Term::App(NOT.to_string(), vec![Term::Const(c.to_owned())])),
                _ => Some(Term::App(NOT.to_string(), vec![Term::App(c.to_owned(), ts.to_owned())])),
            }
        }
    }
}

