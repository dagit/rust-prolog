use std::collections::HashSet;
use gc::Gc;

use syntax::Term;

type InnerHeap = HashSet<Gc<Term>>;
pub struct Heap {
    heap: InnerHeap,
}

impl Heap {
    pub fn new() -> Self {
        Heap { heap: HashSet::new() }
    }

    pub fn insert(&mut self, t: Term) -> Gc<Term>
    {
        let gc_term = Gc::new(t);
        match self.heap.get(&gc_term) {
            Some(gc) => return gc.clone(),
            None     => ()
        }
        self.heap.insert(gc_term.clone());
        gc_term
    }
}
