use std::collections::HashMap;
use std::rc::Rc;
use std::rc::Weak;

use syntax::Term;

type InnerHeap = HashMap<Term,Weak<Term>>;
pub struct Heap {
    heap: InnerHeap,
}

impl Heap {
    pub fn new() -> Self {
        Heap { heap: HashMap::new() }
    }

    pub fn insert(&mut self, t: Term) -> Rc<Term>
    {
        match self.heap.get(&t) {
            Some(ref w) => {
                match w.upgrade() {
                    None     => (),
                    Some(rc) => return rc
                }
            }
            None        => ()
        }
        let r = Rc::new(t.clone());
        self.heap.insert(t, Rc::downgrade(&r));
        r
    }

    pub fn cleanup(&mut self) {
        self.heap.retain(|_, ref y| y.upgrade().is_some());
    }
}
