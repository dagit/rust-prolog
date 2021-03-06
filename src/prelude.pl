# Equality of terms
eq(X,X).

# Lists

## Constructors:
# nil.
# cons(X,Y).

## List relation:
list(nil).
list(cons(X,Y)) :- list(Y).

## List append
append(nil,X,X).
append([H|T], L2, [H|L3]) :- append(T,L2,L3).

## List delete
delete(X,[X|T],T).
delete(X,[H|T],[H|T2]) :- delete(X,T,T2).

## Head & Tail
head(H,[H|T]).
tail(T,[H|T]).

## First and last
first(H,cons(H,T)).
last(Y,cons(H,T)) :- last(Y,T).

## Prefix and suffix
prefix(nil, X).
prefix([H|X],[H|Y]) :- prefix(X,Y).
suffix(X,X).
suffix([H|X],Y) :- suffix(X,Y).

## Membership
member(X, [X|T]).
member(X, [H|L]) :- member(X, L).

## Sublist
sublist(S,L) :- append(X,S,P), append(P,Y,L).

## Permutations
perm(nil,nil).
perm(L,[H|P]) :- delete(H,L,R), perm(R,P).


# Natural Numbers

## Constructors:
# zero.
# succ(X).

## Nat relation:
nat(zero).
nat(succ(X)) :- nat(X).

## Addition:

add(zero,S,S).
add(succ(I),J,succ(K)) :- add(I,J,K).

## Subtraction:

# sub(x,y,z) => x - y = z
sub(S,zero,S).
# if I - J = K, then (I + 1) - (J + 1) = I - J = K.
sub(succ(I), succ(J), K) :- sub(I,J,K).

## Natural number Comparisons
lt(zero,succ(X)).
lt(succ(X), succ(Y)) :- lt(X,Y).

lte(X,X).
lte(X,Y) :- lt(X,Y).

gt(succ(X),zero).
gt(succ(X),succ(Y)) :- gt(X,Y).

gte(X,X).
gte(X,Y) :- gt(X,Y).

