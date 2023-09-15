1. What is a PL?
    - Syntax (abstract)
    - Static Semantics (judgments)
    - Dynamic Semantics (evaluation)

2. Pie definition:

A, B, e ::= (quote <alpha>) | Atom | zero | add1 e | Nat | Pair A B | (cons e e) | (car e) | (cdr e) | U


forms of judgments:

-------------
e is Type

-------------
e : e               -- (e is a e, or e has type e), e is meta-variable here


Actual rules (static semantics):

--------------
Atom is Type


--------------
Nat is Type


---------------
z : Nat


e : Nat
---------------
add1 e : Nat


-----------------------
(quote <alpha>) : Atom


e : A
e' : B
----------------------
(cons e e') : Pair A B

e : Pair A B
----------------------
car e : A

e : Pair A B
----------------------
cdr e : B




Property of the judgment:
Prop1: If e : A then A is Type
Prop2: A : U iff A is Type (this is actually false, because U is a Type, but it does not have a type)
Prop2-refine: e : A then "A is Type", but not the other direction


dynamic semantics (in rewrite semantics):

form of rule:
e --> e

(car (cons e1 e2)) --> e1

(cdr (cons e1 e2)) --> e2




