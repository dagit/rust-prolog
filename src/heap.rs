use std::collections::HashSet;
use std::hash::Hash;
use gc::{Gc,Trace};

use syntax::Term;

type TermSet   = HashSet<Gc<Term>>;
type StringSet = HashSet<Gc<String>>;
pub struct Heap {
    // Values defined at the "top level" should
    // live forever.
    terms:   TermSet,
    strings: StringSet,

    // Values constructed during the search procedure
    // or as the query need only live until the query
    // has been satisfied.
    ephemeral_terms:   TermSet,
    ephemeral_strings: StringSet,
}

#[derive(Hash, Eq, PartialEq, Clone, Copy, Debug)]
pub enum Lifetime {
  Perm,
  Ephemeral,
}

fn insert_thing<A>(perm_heap: &mut HashSet<Gc<A>>,
                   ephemeral_heap: &mut HashSet<Gc<A>>,
                   t: A, lt: Lifetime) -> Gc<A>
    where A: Trace,
          Gc<A>: Eq,
          Gc<A>: Hash
{
        let gc_thing = Gc::new(t);
        match perm_heap.get(&gc_thing) {
            Some(gc) => return gc.clone(),
            None     => match ephemeral_heap.get(&gc_thing) {
                Some(gc) => return gc.clone(),
                None     => (),
            }
        }
        match lt {
            Lifetime::Perm      => perm_heap.insert(gc_thing.clone()),
            Lifetime::Ephemeral => ephemeral_heap.insert(gc_thing.clone()),
        };
        gc_thing
}

impl Heap {
    pub fn new() -> Self {
        Heap {
            terms:   HashSet::new(),
            strings: HashSet::new(),

            ephemeral_terms:   HashSet::new(),
            ephemeral_strings: HashSet::new(),
        }
    }

    pub fn insert_term(&mut self, t: Term, lt: Lifetime) -> Gc<Term>
    {
        insert_thing(&mut self.terms, &mut self.ephemeral_terms, t, lt)
    }

    pub fn insert_string(&mut self, s: String, lt: Lifetime) -> Gc<String>
    {
        insert_thing(&mut self.strings, &mut self.ephemeral_strings, s, lt)
    }

    pub fn cleanup(&mut self){
        self.ephemeral_terms.clear();
        self.ephemeral_strings.clear();
        self.ephemeral_terms.shrink_to_fit();
        self.ephemeral_strings.shrink_to_fit();
        gc::force_collect();
    }
}
