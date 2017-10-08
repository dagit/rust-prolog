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
pub type Clause = Vec<Atom>;

/* An assertion [(a,b_1,...,b_n)] is a Horn formula
[b_1 & ... & b_n => a]. */
pub type Assertion = (Atom, Clause);

/* An environment is a list of pairs [(x, e)] where [x] is a variable
instance and [e] is a term. An environment represents the current values
of variables. */
pub type Environment = HashMap<Variable, Term>;

/* A database is a list of assertions. It represents the current program. */
pub type Database = Vec<Assertion>;

/* Toplevel commands */
#[derive(PartialEq, Clone)]
pub enum ToplevelCmd {
    Assert(Assertion), /* Assertion [a :- b_1, ..., b_n.] or [a.] */
    Goal(Clause),      /* Query [?- a] */
    Quit,              /* The [$quit] command. */
    Use(String)        /* The [$use "filename"] command. */
}

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
fn string_of_term(t: &Term) -> String {
    match *t {
        Term::Var((ref v, 0)) => v.clone(),
        Term::Var((ref v, n)) => v.clone() + &n.to_string(),
        Term::Const(ref c) => c.clone(),
        Term::App(ref f, ref ls) => {
            let mut strings = Vec::with_capacity(ls.len());
            for l in ls.iter() {
                strings.push(string_of_term(l));
            }
            f.clone() + "(" + &strings.join(", ") + ")"
        }
    }
}

/* [string_of_env env] converts environment [env] to its string
representation. It only keeps instance variables at level 0, i.e.,
those that appear in the toplevel goal. */
pub fn string_of_env(env: &Environment) -> String {
    let toplevels = env.iter()
        .filter( |&(&(_,n),_) | n==0)
    /* This creates copies and is unnecessary */
        .map( |(&(ref x,ref y), z)|
                  ((x.clone(),y.clone()),z.clone()) )
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
fn exists<P, A>(predicate: P, ls: &[A]) -> bool
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
