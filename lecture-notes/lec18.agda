U = Set
IsType = Set₁

--------------------------------------------------------------------------
-- Natural Numbers

data Nat : U where
  zero : Nat
  add1 : Nat -> Nat

open import Agda.Primitive

_ : Setω₁
_ = Setω

foo : Setω
foo = {l : Level}
      (motive : (Nat -> Set l)) ->
      (target : Nat) ->
      (base : (motive zero)) ->
      (step : (n-1 : Nat) -> (motive n-1) ->
              (motive (add1 n-1))) ->
      (motive target)

ind-Nat : {l : Level}
          (motive : (Nat -> Set l)) ->
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

-- which-Nat-Type : {X : IsType} -> Nat -> X -> (Nat -> X) -> X
-- which-Nat-Type zero base step = base
-- which-Nat-Type (add1 target) base step = step target

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

impossible : {A : U} -> Absurd -> A
impossible {A} p = ind-Absurd (λ _ -> A) p

-- Negation is the principle of reduction to absurdity
-- https://en.wikipedia.org/wiki/Reductio_ad_absurdum
Not : ∀ {l : Level} -> Set l -> Set l
Not X = X -> Absurd

-- The Consequences of two numbers being equal
≡-Consequence : Nat -> Nat -> U
≡-Consequence n m = which-Nat n
                     (which-Nat m Trivial (λ m-1 -> Absurd))
                     (λ n-1 ->
                        (which-Nat m Absurd (λ m-1 -> (≡ Nat n-1 m-1))))

-- The equality consquence property should always hold about the same natural
-- number and itself.
≡-consequence-same : (n : Nat) -> (≡-Consequence n n)
≡-consequence-same n = ind-Nat (λ x -> ≡-Consequence x x) n sole (λ n-1 _ -> (same n-1))

use-Nat≡ : {n m : Nat} -> (≡ Nat n m) -> (≡-Consequence n m)
use-Nat≡ {n} {m} asm = replace asm (λ x -> (≡-Consequence n x)) (≡-consequence-same n)

-- clearly it is Absurd that zero ≡ add1 n, for any n
zero-not-add1 : {n : Nat} -> ≡ Nat zero (add1 n) -> Absurd
zero-not-add1 {n} asm = (use-Nat≡ asm)

zero=add1-implies-anything : {C : U} -> (n : Nat) -> ≡ Nat zero (add1 n) -> C
zero=add1-implies-anything {C} n asm = ind-Absurd (λ _ -> C) (zero-not-add1 asm)

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
-- Maybe

Maybe : (A : U) -> U
Maybe A = Either A Trivial

just : {A : U} -> (a : A) -> Maybe A
just a = left a

nothing : {A : U} -> Maybe A
nothing = right sole

------------------------------------------------------------------------
-- Fin

-- represents the range [0, n)
Fin : Nat -> U
Fin n = iter-Nat n Absurd (λ Fin-n-1 -> Maybe Fin-n-1)

-- is the proof that 0 ∈ [0, (add1 n))
fzero : (n : Nat) -> Fin (add1 n)
fzero n = nothing

-- is the proof that if m ∈ [0, n), then m ∈ [0, (add1 n))
fadd1 : (n : Nat) -> Fin n -> (Fin (add1 n))
fadd1 n m = just m

------------------------------------------------------------------------
-- Exercise 1
-- Is it true that every proposition is either true or false?

not-pem-false : Not (Not ((X : U) -> Either X (Not X)))
not-pem-false asm = asm λ X' → {!!}
-- this cannot be proved using the strategy for not-pem-false'
-- not-pem-false asm = asm λ X → right (λ x → asm λ X₁ → left {!!})

-- Notice this proof never use false-elim, so we can parametrize over the return type of Not
-- i.e., it doesn't have to be (Not X) but (X -> C) for an arbitrary C
-- This is also suggesting this is NOT a property of false, but a property of implication
--
-- If you remove Absurd type from your TT,
-- it's equivalent to what's called "minimal constructive logic"
not-pem-false' : (X : U) -> Not (Not (Either X (Not X)))
not-pem-false' X asm = asm (right (λ x → asm (left x)))
-- not-pem-false' is really "decidability is not false"

-- ((X \/ X -> Y) -> Y) -> Y
not-pem-false'' : (X Y : U) -> (Either X (X -> Y) -> Y) -> Y
not-pem-false'' X Y asm = asm (right (λ x → asm (left x)))

Dec : U -> U
Dec X = Either X (Not X)

------------------------------------------------------------------------
-- Exercise 2
-- Is it true that some things are either true or false?

zero? : (n : Nat) -> Dec (≡ Nat zero n)
zero? n = ind-Nat (λ x → Dec (≡ Nat zero x)) n (left (same zero)) λ n-1 IH → right zero-not-add1

sym : {X : U} {x y : X} -> (≡ X x y) -> (≡ X y x)

nat=? : (n m : Nat) -> (Dec (≡ Nat n m))
nat=? n = ind-Nat
          (λ i → (j : Nat) -> Dec (≡ Nat i j))
          n
          zero?
          λ n-1 IH j →
            ind-Nat
            (λ j' → Dec (≡ Nat (add1 n-1) j'))
            j
            (right λ x → let asm = sym x in zero-not-add1 asm)
            λ m-1 IH' → let n-1=m-1 = (IH m-1) in
              ind-Either
              (λ _ → Dec (≡ Nat (add1 n-1) (add1 m-1)))
              n-1=m-1
              (λ a → left (cong a add1))
              (λ b → right λ x → b (use-Nat≡ x))

------------------------------------------------------------------------
-- Exercise 3
-- Can we abstract out some of this tedious proving?

refute-by-contradiction : {X : U} -> (Dec X) -> (X -> Not X) -> Not X
refute-by-contradiction (left x) x->~x = λ z → x->~x z z
refute-by-contradiction (right x) x->~x = λ z → x->~x z z

proof-by-constradiction : {X : U} -> (Dec X) -> (Not (Not X)) -> X
proof-by-constradiction (left x) ~~x = x
proof-by-constradiction {X} (right x) ~~x = ind-Absurd (λ _ → X) (~~x x)
