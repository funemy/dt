U = Set

-- Declare the typing rules for constructors:
data Nat : U where
  zero : Nat
  add1 : Nat -> Nat

-- Get an elimination principle for free:
--
-- The elimination principle says:
-- - For each constructor:
--    - Given a computation parameterized by all the arguments to the constructor,
--      return something of some type (X)
--    - Branch on the constructor, then apply the parameterized computation to
--      all the arguments of the constructor, and a recursive call.
--
-- A bunch of math says any function defined from this elimination principle is
-- always terminating.

elim-Nat : {X : U} -> Nat -> X -> (Nat -> X -> X) -> X
elim-Nat zero b s = b
elim-Nat (add1 n) b s = s n (elim-Nat n b s)


-- ... Work together ...

data Pair (A B : U) : U where
  cons : A -> B -> Pair A B

elim-Pair : {A B X : U} -> Pair A B -> (A -> B -> X) -> X
elim-Pair (cons a b) f = f a b

car : {A B : U} -> Pair A B -> A
car p = elim-Pair p (λ a _ -> a)

cdr : {A B : U} -> Pair A B -> B
cdr p = elim-Pair p (λ _ b -> b)

flip : {A B : U} -> Pair A B -> Pair B A
flip p = elim-Pair p (λ a b -> cons b a)

flip' : {A B : U} -> Pair A B -> Pair B A
flip' p = (cons (cdr p) (car p))

open import Relation.Binary.PropositionalEquality

test1 : {A B : U} -> (a : A) -> (b : B) -> flip (cons a b) ≡ flip' (cons a b)
test1 a b = refl

flip-Nat : Pair Nat Nat -> Pair Nat Nat
flip-Nat = flip -- {Nat} {Nat} are unnecessary

id : {X : U} -> X -> X
id x = x

id-Nat : Nat -> Nat
id-Nat = id

twin : {X : U} -> X -> Pair X X
twin x = cons x x

-- Exercise 1: Implement the Law of Lists as an Agda datatype
-- The Law of Lists: If E is a Type, then (List E) is a Type
--
-- You may also need the Law of nil and the law of cons
-- The Law of nil: nil is a (List E), for any E
-- The Law of cons: If e is a E, and es is a (List E), then (cons e es) is a
--   (List E)

data List (E : U) : U where
  nil : List E
  lcons : E -> List E -> List E

-- Exercise 2: Define the eliminator for List

elim-List : {E X : U} -> List E -> (E -> List E -> X -> X) -> X -> X
elim-List nil f x = x
elim-List (lcons hd tl) f x = f hd tl (elim-List tl f x)

-- Let's define length from your eliminator

length : {E : U} -> List E -> Nat
length l = elim-List l ((λ hd tl n -> add1 n)) zero

test2 : length (lcons zero (lcons zero nil)) ≡ (add1 (add1 zero))
test2 = refl

-- Let's define append from your eliminator

append : {E : U} -> List E -> E -> List E
append l e = elim-List l (λ hd tl acc -> lcons hd acc) (lcons e nil)

test3 : append (lcons (add1 zero) nil) zero ≡ (lcons (add1 zero) (lcons zero nil))
test3 = refl
