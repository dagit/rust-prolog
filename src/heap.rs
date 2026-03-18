use std::collections::HashSet;
use std::hash::Hash;
use std::sync::Arc;

use crate::syntax::Term;

type TermSet = HashSet<Arc<Term>>;
type StringSet = HashSet<Arc<String>>;
pub struct Heap {
    // Values defined at the "top level" should
    // live forever.
    terms: TermSet,
    strings: StringSet,

    // Values constructed during the search procedure
    // or as the query need only live until the query
    // has been satisfied.
    ephemeral_terms: TermSet,
    ephemeral_strings: StringSet,
}

#[derive(Hash, Eq, PartialEq, Clone, Copy, Debug)]
pub enum Lifetime {
    Perm,
    Ephemeral,
}

fn insert_thing<A>(
    perm_heap: &mut HashSet<Arc<A>>,
    ephemeral_heap: &mut HashSet<Arc<A>>,
    t: A,
    lt: Lifetime,
) -> Arc<A>
where
    Arc<A>: Eq,
    Arc<A>: Hash,
{
    let arc_thing = Arc::new(t);
    match perm_heap.get(&arc_thing) {
        Some(a) => return a.clone(),
        None => {
            if let Some(a) = ephemeral_heap.get(&arc_thing) {
                return a.clone();
            }
        }
    }
    match lt {
        Lifetime::Perm => perm_heap.insert(arc_thing.clone()),
        Lifetime::Ephemeral => ephemeral_heap.insert(arc_thing.clone()),
    };
    arc_thing
}

impl Default for Heap {
    fn default() -> Self {
        Self::new()
    }
}

impl Heap {
    pub fn new() -> Self {
        Heap {
            terms: HashSet::new(),
            strings: HashSet::new(),

            ephemeral_terms: HashSet::new(),
            ephemeral_strings: HashSet::new(),
        }
    }

    pub fn insert_term(&mut self, t: Term, lt: Lifetime) -> Arc<Term> {
        insert_thing(&mut self.terms, &mut self.ephemeral_terms, t, lt)
    }

    pub fn insert_string(&mut self, s: String, lt: Lifetime) -> Arc<String> {
        insert_thing(&mut self.strings, &mut self.ephemeral_strings, s, lt)
    }

    pub fn cleanup(&mut self) {
        self.ephemeral_terms.clear();
        self.ephemeral_strings.clear();
        self.ephemeral_terms.shrink_to_fit();
        self.ephemeral_strings.shrink_to_fit();
    }
}
