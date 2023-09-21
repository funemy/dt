define evaluator:

Judgement form:

A = B

------------------
z = z : Nat

e1 = e2 : Nat
-------------------------
(add1 e1) = (add1 e2) : Nat


e1 = e1' : A
e2 = e2' : B
------------------------------------------
(cons e1 e2) = (cons e1' e2') : Pair A B


version 1 for lambda:

\forall e : A . e1[x -> e] = e2[x -> e] : B
------------------------------------------
\x. e1 = \x. e2  : A -> B

But the definition above doesn't compute

the rough idea for version 2 is to compare the equivalence of the body

e1 alpha= e2 : B
-----------------------------
\x . e1 = \x . e2 : A -> B
