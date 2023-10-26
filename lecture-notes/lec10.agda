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

--------------------------------------------------------------------------

-- Let's warm up:
car-correct : {A B : U} -> (a : A) -> (b : B) -> (≡ A (car (cons a b)) a)
car-correct a b = same a

cdr-correct : {A B : U} -> (a : A) -> (b : B) -> (≡ B (cdr (cons a b)) b)
cdr-correct a b = same b

-- define which-Pair:
which-Pair : {A B : U} -> {X : U} -> Pair A B -> (A -> B -> X) -> X
which-Pair (cons x x₁) f = f x x₁

car' : ∀ {A B} -> Pair A B -> A
car' p = which-Pair p (λ a b -> a)

cdr' : ∀ {A B} -> Pair A B -> B
cdr' p = which-Pair p (λ a b -> b)

car'-correct : {A B : U} -> (a : A) -> (b : B) -> (≡ A (car' (cons a b)) a)
car'-correct a b = same a

cdr'-correct : {A B : U} -> (a : A) -> (b : B) -> (≡ B (cdr' (cons a b)) b)
cdr'-correct a b = same b

car=car' : {A B : U} -> (a : A) -> (b : B) -> (≡ A (car (cons a b)) (car' (cons a b)))
car=car' a b = same a

cdr=cdr' : {!!}
cdr=cdr' = {!!}

-- A small digression
-- Software Engineering use of equality with interfaces

--------------------------------------------------------------------------

iter-Nat : {X : U} -> Nat -> X -> (X -> X) -> X
iter-Nat {X = X} target base step = ind-Nat (λ _ -> X) target base (λ _ IH -> step IH)

incr : Nat -> Nat
incr n = (iter-Nat n one (+ one))

cong : {A B : U} -> {x y : A}
     -> (≡ A x y) -> (f : A -> B) -> (≡ B (f x) (f y))
cong (same x) f = same (f x)

-- Let's do a proof:
-- Will this be trivial, or not?
incr=add1 : (n : Nat) -> ≡ Nat (incr n) (add1 n)
incr=add1 n = ind-Nat (λ x -> ≡ Nat (incr x) (add1 x)) n (same (add1 zero)) (λ n-1 IH -> cong IH add1)

twice : Nat -> Nat
twice n = iter-Nat n zero (+ two)

double : Nat -> Nat
double n = + n n

twice=double : {!!}
