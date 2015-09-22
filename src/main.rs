pub mod syntax;
pub mod unify;
pub mod solve;

use solve::{solve_toplevel};

fn main() {
    use syntax::Term;
    use syntax::Term::{Var, Const};
    use syntax::Clause;
    println!("Hello, world!");
    fn mk_const(s: &str) -> Term {
      Const(s.to_string())
    }
    let db = vec![
      /* likes(mary, food). */
      (("likes".to_string(),
        vec![mk_const("mary"), mk_const("food")]), vec![]),
      /* likes(mary, wine). */
      (("likes".to_string(),
        vec![mk_const("mary"), mk_const("wine")]), vec![]),
      /* likes(john, wine). */
      (("likes".to_string(),
        vec![mk_const("john"), mk_const("wine")]), vec![]),
      /* likes(john, mary). */
      (("likes".to_string(),
        vec![mk_const("john"), mk_const("mary")]), vec![]),
    ];
    let clause : Clause = vec![
      /* ?- likes(mary, food). */
      ("likes".to_string(),
        vec![mk_const("mary"), mk_const("food")])
    ];
    /* yes */
    solve_toplevel(&db, &clause);

    let clause : Clause = vec![
      /* ?- likes(john, wine). */
      ("likes".to_string(),
        vec![mk_const("john"), mk_const("wine")])
    ];
    /* yes */
    solve_toplevel(&db, &clause);

    let clause : Clause = vec![
      /* ?- likes(john, food). */
      ("likes".to_string(),
        vec![mk_const("john"), mk_const("food")])
    ];
    /* no */
    solve_toplevel(&db, &clause);

    /* More interesting example */
    /* ?- likes(X,food). */
    let clause : Clause = vec![
      /* ?- likes(X, wine). */
      ("likes".to_string(),
        vec![Var(("X".to_string(), 0)), mk_const("wine")])
    ];
    solve_toplevel(&db, &clause);

}
