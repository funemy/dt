e : B
A = B
------------(conv)
e : A

example:
...
-------------------------
0 : (car (cons Nat Nat))

Now we have a new judgment form |e1 = e2 : A| to express the A=B judgment above.

But this new judgement has a problem, consider the case (Pair U U), when we want to say (Pair U U) = (Pair U U) : ?, we cannot annotate a type for (Pair U U).

The way to solve this is to introduce a new kind of judgment, |A = B Type|, meaning A and B are the same type.
The rationale is that for things like (Pair U U) is a Type, but it's not a U.

So that we can refine the (conv) rule into:

e : B
A = B Type
-------------
e : A


Some other new rules:

---------------------
Trivial : U


---------------------
sole : Trivial


beta-rule (reduction-like rules):

e1 = e1' : A
e2 : B
------------------------------
(car (cons e1 e2)) = e1' : A

eta-rule:

--------------------------------------
e = (cons (car e) (cdr e)) : Pair A B

with type information, we have more information when deciding the sameness of an exrepssion, for example:

-----------------------------------
e = sole : Trivial


=========================================

-----------------------------------
e = e : A
