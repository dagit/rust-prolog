use std::sync::Arc;

use crate::heap::{Heap, Lifetime};
use crate::syntax::{occurs, subst_term, Atom, Environment, Term};

/* [NoUnify] is used when terms cannot be unified. */
pub struct NoUnify;

/* [unify_terms env t1 t2] unifies terms [t1] and [t2] in the current
environment [env]. On success it returns the environment extended with
the result of unification. On failure it raises [NoUnify]. */
pub fn unify_terms(
    env: &Environment,
    heap: &mut Heap,
    t1: &Term,
    t2: &Term,
) -> Result<Environment, NoUnify> {
    let new_t1 = subst_term(env, heap, t1);
    let new_t2 = subst_term(env, heap, t2);
    if new_t1 == new_t2 {
        Ok(env.clone())
    } else {
        match (&*new_t1, &*new_t2) {
            (&Term::Var(ref y), t) | (t, &Term::Var(ref y)) => {
                if occurs(y, t) {
                    Err(NoUnify)
                } else {
                    let mut new_env = env.clone();
                    new_env.insert(y.clone(), heap.insert_term(t.clone(), Lifetime::Ephemeral));
                    Ok(new_env)
                }
            }
            (Term::App(c1, ts1), Term::App(c2, ts2)) => {
                if c1 == c2 {
                    unify_lists(env, heap, ts1, ts2)
                } else {
                    Err(NoUnify)
                }
            }
            (&Term::Const(_), _) | (_, _) => Err(NoUnify),
        }
    }
}

/* [unify_lists env lst1 lst2] unifies two lists of terms in current
environment [env] and returns a new environment [env'] on success. It
returns [NoUnify] on failure or if the lists are not equal length.
 */
fn unify_lists(
    env: &Environment,
    heap: &mut Heap,
    lst1: &[Arc<Term>],
    lst2: &[Arc<Term>],
) -> Result<Environment, NoUnify> {
    if lst1.len() != lst2.len() {
        Err(NoUnify)
    } else {
        lst1.iter()
            .zip(lst2.iter())
            .try_fold(env.clone(), |new_env, (l1, l2)| {
                unify_terms(&new_env, heap, l1, l2)
            })
    }
}

/* [unify_atoms env a1 a2] unifies atomic propositions [a1] and [a2]
in current environment [env] and returns a new environment [env'] on
success. It raises [NoUnify] on failure. */
pub fn unify_atoms(
    env: &Environment,
    heap: &mut Heap,
    (c1, ts1): &Atom,
    (c2, ts2): &Atom,
) -> Result<Environment, NoUnify> {
    if c1 == c2 {
        unify_lists(env, heap, ts1, ts2)
    } else {
        Err(NoUnify)
    }
}
