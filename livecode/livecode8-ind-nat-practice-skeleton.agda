U = Set

data Nat : U where
  zero : Nat
  add1 : Nat -> Nat

data Vec (A : U) : Nat -> U where
  vecnil : Vec A zero
  veccons : (n : Nat) -> A -> Vec A n -> Vec A (add1 n)

-- Head and tail from the book, axiomatized for now
head : (A : U) -> (n : Nat) -> (Vec A (add1 n)) -> A
head = {!!}

tail : (A : U) -> (n : Nat) -> (Vec A (add1 n)) -> (Vec A n)
tail = {!!}

ind-Nat : {!!}
ind-Nat = {!!}
ind-Nat = {!!}

drop-last : (A : U) -> (n : Nat) -> Vec A (add1 n) -> (Vec A n)
drop-last = {!!}

-- Lets define plus real quick
_+_ : Nat -> Nat -> Nat
n + m = ind-Nat {!!} {!!} {!!} {!!}


one = add1 zero
two = add1 one
three = add1 two
four = add1 three

module test where
  open import Relation.Binary.PropositionalEquality

  test1 : two ≡ (one + one)
  test1 = refl

  test2 : four ≡ (two + two)
  test2 = refl


-- Let's implement that equality type

-- claim1 : U
-- claim1 = (≡ Nat (+ one one) two)

-- open import Data.String
-- Atom = String
--
-- claim2 : U
-- claim2 = (≡ Atom "kale" "blackberries")

data Pair A B : U where
  cons : A -> B -> Pair A B

car : ∀ {A B} -> Pair A B -> A
car (cons x x₁) = x

cdr : ∀ {A B} -> Pair A B -> B
cdr (cons x x₁) = x₁

-- claim3 : U
-- claim3 = (≡ (car (cons Nat Atom)) two (+ one one))


-- Let's prove some things

-- thm1 : claim1

+1=add1 : {!!}


incr=add1 : {!!}


-- Rework these in Pie, using TODO as necessary.
