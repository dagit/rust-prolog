# Equality of terms
eq(X,X).

# Lists

## Constructors:
nil.
cons(X,Y).

## List relation:
list(nil).
list(cons(X,Y)) :- list(Y).

## List append
append(nil,X,X).
append(cons(H,T), L2, cons(H,L3)) :- append(T,L2,L3).

# Naturals

## Constructors:
zero.
succ(X).

## Nat relation:
nat(zero).
nat(succ(X)) :- nat(X).
