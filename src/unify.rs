use std::sync::Arc;

use crate::heap::{Heap, Lifetime};
use crate::syntax::{occurs, subst_term, Atom, Environment, Term};

/* [NoUnify] is used when terms cannot be unified. */
#[derive(Debug)]
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::tests::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn unify_reflexive(t in arb_term(3)) {
            let mut heap = Heap::new();
            let env = im::HashMap::new();
            prop_assert!(unify_terms(&env, &mut heap, &t, &t).is_ok());
        }
    }

    proptest! {
        #[test]
        fn unify_symmetric(t1 in arb_term(3), t2 in arb_term(3)) {
            let mut heap1 = Heap::new();
            let mut heap2 = Heap::new();
            let env = im::HashMap::new();

            let result = unify_terms(&env, &mut heap1, &t1, &t2);
            prop_assume!(result.is_ok());
            prop_assert!(unify_terms(&env, &mut heap2, &t2, &t1).is_ok());
        }
    }

    proptest! {
        #[test]
        fn occurs_check(x in arb_variable(), t in arb_term(3)) {
            let mut heap = Heap::new();
            let env = im::HashMap::new();
            let c = Arc::new("f".to_owned());
            let var_x = Arc::new(Term::Var(x.clone()));
            let t_with_x = Arc::new(Term::App(c, vec![var_x, t]));
            prop_assert!(unify_terms(&env, &mut heap, &Term::Var(x), &t_with_x).is_err());
        }
    }

    proptest! {
        #[test]
        fn unify_consistent_substitution(t1 in arb_term(3), t2 in arb_term(3)) {
            let mut heap = Heap::new();
            let env = im::HashMap::new();
            let result = unify_terms(&env, &mut heap, &t1, &t2);
            prop_assume!(result.is_ok());
            let unified_env = result.unwrap();
            let s1 = subst_term(&unified_env, &mut heap, &t1);
            let s2 = subst_term(&unified_env, &mut heap, &t2);
            prop_assert_eq!(s1, s2);
        }
    }

    proptest! {
        #[test]
        fn unify_lists_length_mismatch(
            t1 in arb_term(2),
            t2 in arb_term(2),
            t3 in arb_term(2),
        ) {
            let mut heap = Heap::new();
            let env = im::HashMap::new();
            // 1-element list vs 2-element list should always fail
            let short = vec![t1.clone()];
            let long = vec![t2, t3];
            prop_assert!(unify_lists(&env, &mut heap, &short, &long).is_err());
        }
    }

    proptest! {
        #[test]
        fn unify_atoms_functor_mismatch(
            c1 in arb_constant(),
            c2 in arb_constant(),
            args in proptest::collection::vec(arb_term(2), 0..3),
        ) {
            prop_assume!(c1 != c2);
            let mut heap = Heap::new();
            let env = im::HashMap::new();
            let a1 = (c1, args.clone());
            let a2 = (c2, args);
            prop_assert!(unify_atoms(&env, &mut heap, &a1, &a2).is_err());
        }
    }
}
