use std::collections::HashSet;
use std::hash::Hash;
use gc::{Gc,Trace};

use syntax::Term;

type TermSet   = HashSet<Gc<Term>>;
type StringSet = HashSet<Gc<String>>;
pub struct Heap {
    terms:   TermSet,
    strings: StringSet,
}

fn insert_thing<A>(heap: &mut HashSet<Gc<A>>, t: A) -> Gc<A>
    where A: Trace,
          Gc<A>: Eq,
          Gc<A>: Hash
{
        let gc_thing = Gc::new(t);
        match heap.get(&gc_thing) {
            Some(gc) => return gc.clone(),
            None     => ()
        }
        heap.insert(gc_thing.clone());
        gc_thing
}

impl Heap {
    pub fn new() -> Self {
        Heap {
            terms:   HashSet::new(),
            strings: HashSet::new(),
        }
    }

    pub fn insert_term(&mut self, t: Term) -> Gc<Term>
    {
        insert_thing(&mut self.terms, t)
    }

    pub fn insert_string(&mut self, s: String) -> Gc<String>
    {
        insert_thing(&mut self.strings, s)
    }
}
