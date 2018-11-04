# Sorting
naive_sort(L,S) :- perm(L,S), is_sorted(S).

is_sorted(nil).
is_sorted(cons(X,nil)).
is_sorted(cons(X,[Y|T])) :- lte(X,Y), is_sorted([Y|T]).

?- naive_sort([2, 1, 0], X).
