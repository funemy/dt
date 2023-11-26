U = Set
IsType = Set₁

--------------------------------------------------------------------------
-- Natural Numbers

data Nat : U where
  zero : Nat
  add1 : Nat -> Nat

open import Agda.Primitive

ind-Nat : {l : Level} (motive : (Nat -> Set l)) ->
          (target : Nat) ->
          (base : (motive zero)) ->
          (step : (n-1 : Nat) -> (motive n-1) ->
                  (motive (add1 n-1))) ->
          (motive target)
ind-Nat motive zero base step = base
ind-Nat motive (add1 j-1) base step = (step j-1 (ind-Nat motive j-1 base step))


iter-Nat : {l : Level} {X : Set l} -> Nat -> X -> (X -> X) -> X
iter-Nat {l} {X} target base step = ind-Nat (λ _ -> X) target base (λ _ IH -> (step IH))

which-Nat : {l : Level} {X : Set l} -> Nat -> X -> (Nat -> X) -> X
which-Nat zero base step = base
which-Nat  (add1 target) base step = step target

which-Nat-Type : {X : IsType} -> Nat -> X -> (Nat -> X) -> X
which-Nat-Type zero base step = base
which-Nat-Type (add1 target) base step = step target

+ : Nat -> Nat -> Nat
+ n m = ind-Nat (λ i -> Nat) n m (λ _ acc -> (add1 acc))

one = add1 zero
two = add1 one
three = add1 two
four = add1 three
five = add1 four

double : Nat -> Nat
double n = iter-Nat n zero (+ two)

--------------------------------------------------------------------------
-- Dependent Pair
data Σ (A : U) (B : A -> U) : U where
  cons : (a : A) -> (B a) -> Σ A B

car : ∀ {A B}  -> Σ A B -> A
car (cons x x₁) = x

cdr : ∀ {A B} -> (p : Σ A B) -> (B (car p))
cdr (cons x x₁) = x₁

--------------------------------------------------------------------------
-- Equality
data ≡ (X : U) : X -> X -> U where
  same : (from : X) -> ≡ X from from

cong : {A B : U} -> {x y : A} ->
      (≡ A x y) -> (f : A -> B) -> (≡ B (f x) (f y))
cong (same from) f = (same (f from))

replace : {X : U} {from to : X} ->
          (≡ X from to) ->
          (motive : (X -> U)) ->
          (motive from) ->
          (motive to)
replace (same _) motive a = a

------------------------------------------------------------------------
-- Either

data Either (A : U) (B : U) : U where
  left : A -> Either A B
  right : B -> Either A B

test : U
test = Either (Either (Either Nat Nat) Nat) Nat

ind-Either : {A B : U}
  (motive : Either A B -> U) ->
  (target : Either A B) ->
  (base-left : (a : A) -> (motive (left a)))
  (base-right : (b : B) -> (motive (right b))) ->
  (motive target)
ind-Either motive (left x) base-left base-right = base-left x
ind-Either motive (right x) base-left base-right = base-right x

------------------------------------------------------------------------
-- Trivial

data Trivial : U where
  sole : Trivial

Bool = Either Trivial Trivial

true : Bool
true = left sole

false : Bool
false = right sole

if : {A : U} -> Bool -> A -> A -> A
if {A} target con alt = ind-Either (λ _ -> A) target (λ _ -> con) (λ _ -> alt)

------------------------------------------------------------------------
-- Absurd is the type that cannot be constructed.

data Absurd : U where

-- Logically, the (constructive) principle of explosion
-- https://en.wikipedia.org/wiki/Principle_of_explosion
--
-- Computationally, represents well typed dead code: something like
-- `assert impossible`
ind-Absurd : (motive : Absurd -> U) ->
  (target : Absurd) ->
  (motive target)
ind-Absurd motive ()

-- Negation is the principle of reduction to absurdity
-- https://en.wikipedia.org/wiki/Reductio_ad_absurdum
Not : U -> U
Not X = X -> Absurd

-- The Consequences of two numbers being equal
≡-Consequence : Nat -> Nat -> U
≡-Consequence n m = which-Nat-Type n
                     (which-Nat-Type m Trivial (λ m-1 -> Absurd))
                     (λ n-1 ->
                        (which-Nat-Type m Absurd (λ m-1 -> (≡ Nat n-1 m-1))))

-- The equality consquence property should always hold about the same natural
-- number and itself.
≡-consequence-same : (n : Nat) -> (≡-Consequence n n)
≡-consequence-same n = ind-Nat (λ x -> ≡-Consequence x x) n sole (λ n-1 _ -> (same n-1))

use-Nat≡ : (n m : Nat) -> (≡ Nat n m) -> (≡-Consequence n m)
use-Nat≡ n m asm = replace asm (λ x -> (≡-Consequence n x)) (≡-consequence-same n)

-- clearly it is Absurd that zero ≡ add1 n, for any n
zero-not-add1 : (n : Nat) -> ≡ Nat zero (add1 n) -> Absurd
zero-not-add1 n asm = (use-Nat≡ zero (add1 n) asm)

zero=add1-implies-anything : (C : U) -> (n : Nat) -> ≡ Nat zero (add1 n) -> C
zero=add1-implies-anything C n asm = ind-Absurd (λ _ -> C) (zero-not-add1 n asm)

------------------------------------------------------------------------
-- Lists

data List (A : U) : U where
  nil : List A
  listcons : A -> List A -> List A

ind-List : {A : U} ->
          (target : List A)
          (motive : List A -> U) ->
          (base : (motive nil)) ->
          (step : (a : A) -> (tail : List A) -> (ih : (motive tail)) ->
                  (motive (listcons a tail))) ->
          (motive target)
ind-List nil motive base step = base
ind-List (listcons x target) motive base step = step x target (ind-List target motive base step)

------------------------------------------------------------------------
-- Vectors, again

data Vec (A : U) : Nat -> U where
  vecnil : Vec A zero
  veccons : (n : Nat) -> A -> Vec A n -> Vec A (add1 n)

ind-Vec : {A : U} ->
          (n : Nat) ->
          (target : Vec A n)
          (motive : (n : Nat) -> Vec A n -> U) ->
          (base : (motive zero vecnil)) ->
          (step : (n-1 : Nat) -> (a : A) -> (tail : Vec A n-1) -> (ih : (motive n-1 tail)) ->
                  (motive (add1 n-1) (veccons n-1 a tail))) ->
          (motive n target)
ind-Vec .zero vecnil motive base step = base
ind-Vec .(add1 n) (veccons n x target) motive base step = step n x target (ind-Vec n target motive base step)


------------------------------------------------------------------------
-- Exercise 1
-- How do we safely project from a list?

Maybe : (A : U) -> U
Maybe A = Either A Trivial

just : {A : U} -> (a : A) -> Maybe A
just a = left a

nothing : {A : U} -> Maybe A
nothing = right sole

list-ref : {A : U} -> (m : Nat) -> List A -> Maybe A

module list-ref-tests where
  _ : ≡ (Maybe Nat) (just three) (list-ref zero (listcons three (listcons four (listcons five nil))))
  _ = {!!}

  _ : ≡ (Maybe Nat) (just four) (list-ref one (listcons three (listcons four (listcons five nil))))
  _ = {!!}

  _ : ≡ (Maybe Nat) (just five) (list-ref two (listcons three (listcons four (listcons five nil))))
  _ = {!!}

------------------------------------------------------------------------
-- Exercise 2
-- How do we safely project from a vector an element we know it exists?
Fin : Nat -> U
Fin n = iter-Nat n Absurd λ Fin-n-1 → Maybe Fin-n-1

-- proof that 0 ∈ [0, (add1 n))
fzero : (n : Nat) -> Fin (add1 n)
fzero n = nothing

-- proof that if m ∈ [0, n), then m ∈ [0, (add1 n))
fadd1 : (n : Nat) -> Fin n -> Fin (add1 n)
fadd1 n m = just m

impossible : {A : U} -> Absurd -> A
impossible {A} e = ind-Absurd (λ _ -> A) e

vec-ref : {A : U} -> {n : Nat} -> (m : Fin n) -> Vec A n -> A
vec-ref {A} {n} m v =
  (ind-Vec n v
    (λ i v -> (Fin i -> A))
    impossible
    λ n-1 a tail ih m-add1 →
      ind-Either (λ _ → A) m-add1 ih (λ b → a))
    m

module vec-ref-tests where
  _ : ≡ Nat three (vec-ref (fzero two) (veccons two three (veccons one four (veccons zero five vecnil))))
  _ = same (add1 (add1 (add1 zero)))

  _ : ≡ Nat four (vec-ref (fadd1 two (fzero one)) (veccons two three (veccons one four (veccons zero five vecnil))))
  _ = same (add1 (add1 (add1 (add1 zero))))

  _ : ≡ Nat five (vec-ref (fadd1 two (fadd1 one (fzero zero))) (veccons two three (veccons one four (veccons zero five vecnil))))
  _ = same (add1 (add1 (add1 (add1 (add1 zero)))))
