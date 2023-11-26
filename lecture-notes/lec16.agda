
U = Set

--------------------------------------------------------------------------

data Nat : U where
  zero : Nat
  add1 : Nat -> Nat

ind-Nat : (motive : (Nat -> U)) ->
          (target : Nat) ->
          (base : (motive zero)) ->
          (step : (n-1 : Nat) -> (motive n-1) ->
                  (motive (add1 n-1))) ->
          (motive target)
ind-Nat motive zero base step = base
ind-Nat motive (add1 j-1) base step = (step j-1 (ind-Nat motive j-1 base step))


iter-Nat : {X : U} -> Nat -> X -> (X -> X) -> X
iter-Nat {X = X} target base step = ind-Nat (λ _ -> X) target base (λ _ IH -> (step IH))

+ : Nat -> Nat -> Nat
+ n m = ind-Nat (λ i -> Nat) n m (λ _ acc -> (add1 acc))

one = add1 zero
two = add1 one
three = add1 two
four = add1 three
five = add1 four

double : Nat -> Nat
double n = iter-Nat n zero (+ two)

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
replace from≡to m = {!!}

------------------------------------------------------------------------

-- Let's prove some properties about some data type.
-- ... what's a property?

Property : (U -> Set₁)
Property = (λ X -> (X -> U))

EqualNat : Property Nat
-- EqualNat = λ n → ≡ Nat n n
EqualNat n = ≡ Nat n n

BiggerThan : Property Nat
-- BiggerThan = λ n -> Σ Nat (λ m -> ≡ Nat (add1 n) m)
BiggerThan = λ n -> ≡ Nat (add1 n) n

Even : Property Nat
Even = λ n -> Σ Nat (λ m -> ≡ Nat n (double m))

Even' : Nat -> U
Even' = λ n -> Σ Nat (λ half -> ≡ Nat n (double half))

--

zero-is-even : Even zero
zero-is-even = cons zero (same zero)

one-is-even : Even one
one-is-even = cons zero {!!}

Odd : Nat -> U
Odd = λ n -> Σ Nat (λ half -> ≡ Nat n (add1 (double half)))

one-is-odd : Odd one
one-is-odd = cons zero (same (add1 zero))

add1-even-odd : (n : Nat) -> (Even n) -> (Odd (add1 n))
add1-even-odd n Pn = let half-n = car Pn in
  let Phalf = (cdr Pn) in
  cons half-n (cong Phalf add1)

add1-odd-even : (n : Nat) -> (Odd n) -> (Even (add1 n))
add1-odd-even n Pn = cons (add1 (car Pn)) (cong (cdr Pn) add1)

-- ≡ Nat (add1 n) (add1 (add1 (double (car Pn))))

-- ≡ Nat n (add1 (double (car Pn)))
-- (cdr ... (Odd n))

--
-- odd-or-even : (n : Nat) -> Either (Odd n) (Even n)


-- Digression

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

data Trivial : U where
  sole : Trivial

Bool = Either Trivial Trivial

true : Bool
true = left sole

false : Bool
false = right sole

if : {A : U} -> Bool -> A -> A -> A
if {A} target con alt = ind-Either (λ _ -> A) target (λ _ -> con) (λ _ -> alt)

--
odd-or-even : (n : Nat) -> Either (Odd n) (Even n)
odd-or-even n = ind-Nat (λ x -> Either (Odd x) (Even x)) n
  (right (cons zero (same zero)))
  (λ n-1 Pn-1 → ind-Either (λ _ -> Either (Odd (add1 n-1)) (Even (add1 n-1))) Pn-1
    (λ Pn-1-odd → right (add1-odd-even n-1 Pn-1-odd))
    (λ Pn-1-even → left (add1-even-odd n-1 Pn-1-even)))

--

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

-- Σ Nat (λ half → ≡ Nat zero (add1 (double half)))
-- clearly true that this is absurd.. but how do we *prove* it?
IsType = Set₁

which-Nat-Type : {X : IsType} -> Nat -> X -> (Nat -> X) -> X
which-Nat-Type {X} zero base step = base
which-Nat-Type {X} (add1 n) base step = step n

≡-Consequence : Nat -> Nat -> U
≡-Consequence n m =
  which-Nat-Type
    n
    (which-Nat-Type m Trivial (λ m-1 → Absurd))
    λ n-1 -> which-Nat-Type m Absurd (λ m-1 -> ≡ Nat n-1 m-1)

-- sanity check
≡-consequence-same : (n : Nat) -> (≡-Consequence n n)
≡-consequence-same n = ind-Nat (λ x -> ≡-Consequence x x) n sole λ n-1 x → same n-1

test1 : {n : Nat} -> (≡ Nat zero (add1 n)) -> (≡-Consequence zero (add1 n))
test1 asm = replace asm (λ x → ≡-Consequence zero x) sole

use-Nat≡ : (n m : Nat) -> (≡ Nat n m) -> (≡-Consequence n m)
use-Nat≡ n m asm = replace asm (λ x → ≡-Consequence n x) (≡-consequence-same n)

zero-not-add1 : (n : Nat) -> Not (≡ Nat zero (add1 n))
zero-not-add1 n asm = use-Nat≡ zero ((add1 n)) asm

zero-not-odd : Not (Odd zero)
zero-not-odd oddz = use-Nat≡ zero (add1 (double (car oddz))) (cdr oddz)

one-not-even : Not (Even one)
one-not-even oneEven =
  ind-Either (λ x → Absurd) (lemma (car oneEven))
    (λ A → let x = replace A (λ x -> ≡ Nat (add1 zero) x) (cdr oneEven) in use-Nat≡ (add1 zero) zero x)
    λ B → let x = replace (cdr B) (λ x → ≡ Nat (add1 zero) x) (cdr oneEven) in
      use-Nat≡ zero ((add1 (car B))) (use-Nat≡ ((add1 zero)) ((add1 (add1 (car B)))) x)
  where
    lemma : (m : Nat) -> Either (≡ Nat (double m) zero) (Σ Nat (λ n -> (≡ Nat (double m) (add1 (add1 n)))))
    lemma m =
      ind-Nat
      (λ x → Either (≡ Nat (double x) zero) (Σ Nat (λ n -> (≡ Nat (double x) (add1 (add1 n))))))
      m
      (left (same zero))
      λ n-1 ih → right (cons (double n-1) (same (add1 (add1 (double n-1)))))
