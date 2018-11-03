# Sorting
naive_sort(L,S) :- perm(L,S), is_sorted(S).

is_sorted(nil).
is_sorted(cons(X,nil)).
is_sorted(cons(X,cons(Y,T))) :- lte(X,Y), is_sorted(cons(Y,T)).

?- naive_sort(
    cons(succ(succ(zero)), cons(succ(zero), cons(zero,nil))),
    X).
