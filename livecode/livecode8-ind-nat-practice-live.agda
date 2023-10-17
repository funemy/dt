U = Set

data Nat : U where
  zero : Nat
  add1 : Nat -> Nat

data Vec (A : U) : Nat -> U where
  vecnil : Vec A zero
  veccons : (n : Nat) -> A -> Vec A n -> Vec A (add1 n)

-- Head and tail from the book, axiomatized for now
head : {A : U} -> (n : Nat) -> (Vec A (add1 n)) -> A
head n (veccons .n x v) = x

tail : {A : U} -> (n : Nat) -> (Vec A (add1 n)) -> (Vec A n)
tail n (veccons .n x v) = v

ind-Nat : (motive : (Nat -> U)) ->
          (target : Nat) ->
          (base : (motive zero)) ->
          (step : (n-1 : Nat) -> (motive n-1) ->
                  (motive (add1 n-1))) ->
          (motive target)
ind-Nat motive zero base step = base
ind-Nat motive (add1 j-1) base step = (step j-1 (ind-Nat motive j-1 base step))

drop-last : (A : U) -> (n : Nat) -> Vec A (add1 n) -> (Vec A n)
drop-last = {!!}

-- Lets define plus real quick
+ : Nat -> Nat -> Nat
-- + n = ind-Nat (λ i -> (Nat -> Nat)) n (λ j -> j) (λ j-1 f -> (λ m -> (f (add1 m))))
+ n m = ind-Nat (λ i -> Nat) n m (λ _ acc -> (add1 acc))

+' : Nat -> Nat -> Nat
+' n = ind-Nat (λ i -> (Nat -> Nat)) n (λ j -> j) (λ j-1 f -> (λ m -> (f (add1 m))))

one = add1 zero
two = add1 one
three = add1 two
four = add1 three

module test where
  open import Relation.Binary.PropositionalEquality

  test1 : two ≡ (+ one one)
  test1 = refl

  test2 : four ≡ (+ two two)
  test2 = refl


-- Let's implement that equality type
data ≡ (X : U) : (from : X) -> (to : X) -> U where
  same : (the : X) -> (≡ X the the)

claim1 : U
claim1 = (≡ Nat (+ one one) two)

claim1' : U
claim1' = (≡ Nat (+ one one) four)

proof1 : claim1
proof1 = same two

-- proof1' : claim1'
-- proof1' = same ?

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

+1=add1 : ≡ (Nat -> Nat) (λ n -> (+ one n)) add1
+1=add1 = same (+ one)

-- +1=add1' : ≡ (Nat -> Nat) (λ m -> (+ m one)) add1
-- +1=add1' = same (+ one)

-- +1=add1' : ≡ (Nat -> Nat) (λ m -> (+' m one)) add1
-- +1=add1' = same (+' one)

right-identity : (m : Nat) -> ≡ Nat (+ zero m) (+ m zero)
right-identity = {!!}

plus-comm : (n m : Nat) -> (≡ Nat (+ n m) (+ m n))
plus-comm n m = (ind-Nat (λ x → (≡ Nat (+ x m) (+ m x))) n (right-identity m) {!!})

-- Goal: (n-1 : Nat) →
--       ≡ Nat (+ n-1 m) (+ m n-1) → ≡ Nat (+ (add1 n-1) m) (+ m (add1 n-1))


incr=add1 : {!!}
-- Rework these in Pie, using TODO as necessary.
