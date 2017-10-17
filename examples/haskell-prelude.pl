# Booleans
type(true, bool).
type(false, bool).

# Maybe
type(nothing, maybe(A)).
type(just, arr(A,maybe(A))).
type(maybe_, arr(B,arr(arr(A,B),arr(maybe(A),B)))).

# Either
type(left, arr(A,either(A,B))).
type(right, arr(B,either(A,B))).
type(either, arr(arr(A, C), arr(arr(B, C), arr(either(A,B), C)))).

# Char TODO: how to represent chars?
type(char,char).

# tuples
type(fst, arr(tuple(A,B),A)).
type(comma,arr(A,arr(B,tuple(A,B)))).
# No idea why this rule for tuple is neccesary
type(app(comma,X),arr(B,tuple(A,B))) :-
    type(X,A).
type(snd, arr(tuple(A,B),B)).
type(curry, arr(arr(tuple(A,B), C), arr(A, arr(B, C)))).
type(uncurry, arr(arr(A, arr(B, C)), arr(tuple(A,B), C))).

type(compose, arr(arr(B, C), arr(arr(A, B), arr(A, C)))).

# function application
type(app(F,X), B) :-
    type(F, arr(A,B)),
    type(X, A).
