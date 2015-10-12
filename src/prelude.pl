# Equality of terms
eq(X,X).

# Lists

## Constructors:
nil.
cons(X,Y).

## List relation:
list(nil).
list(cons(X,Y)).

## List append
append(nil,X,X).
append(cons(H,T), L2, cons(H,L3)) :- append(T,L2,L3).

## List delete
delete(X,cons(X,T),T).
delete(X,cons(H,T),cons(H,T2)) :- delete(X,T,T2).

## Head & Tail
head(H,cons(H,T)).
tail(T,cons(H,T)).

## First and last
first(H,cons(H,T)).
last(Y,cons(H,T)) :- last(Y,T).

## Prefix and suffix
prefix(nil, X).
prefix(cons(H,X),cons(H,Y)) :- prefix(X,Y).
suffix(X,X).
suffix(cons(H,X),Y) :- suffix(X,Y).

## Membership
member(X, cons(X,T)).
member(X, cons(H,L)) :- member(X, L).

## Sublist
sublist(S,L) :- append(X,S,P), append(P,Y,L).

## Permutations
perm(nil,nil).
perm(L,cons(H,P)) :- delete(H,L,R), perm(R,P).


# Natural Numbers

## Constructors:
zero.
succ(X).

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
lt(X,succ(Y)) :- lt(X,Y).

lte(X,X).
lte(X,Y) :- lt(X,Y).

gt(succ(X),zero).
gt(succ(X),Y) :- gt(X,Y).

gte(X,X).
gte(X,Y) :- gt(X,Y).

