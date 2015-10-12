# Sorting
naive_sort(L,S) :- perm(L,S), is_sorted(S).

is_sorted(nil).
is_sorted(cons(X,nil)).
is_sorted(cons(X,cons(Y,T))) :- lte(X,Y), is_sorted(T).

# This nearly overflows the stack, asking for a second answer
# will likely overflow the stack.
?- naive_sort(
    cons(succ(succ(zero)), cons(succ(zero), cons(zero,nil))),
    X).
