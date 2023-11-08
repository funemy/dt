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
          (motive to) ->
          (motive from)
replace (same _) m mto = mto

------------------------------------------------------------------------
-- Let's prove some properties about some data type.
-- ... what's a property?

Property : U -> Set₁
Property X = X -> U

EqualtyNat : Property Nat
EqualtyNat n = ≡ Nat n n

BiggerThan : Property Nat
BiggerThan n = Σ Nat (λ m -> ≡ Nat (add1 n) m)

Even : Property Nat
Even n = Σ Nat (λ m -> ≡ Nat n (double m))

zero-is-even : Even zero
zero-is-even = cons zero (same zero)

Odd : Property Nat
Odd n = Σ Nat (λ m -> ≡ Nat n (add1 (double m)))

one-is-odd : Odd one
one-is-odd = cons zero ((same (add1 zero)))

add1-even-odd : (n : Nat) -> (Even n) -> (Odd (add1 n))
add1-even-odd n even = cons ((car even)) (cong (cdr even) add1)

add1-odd-even : (n : Nat) -> (Odd n) -> (Even (add1 n))
add1-odd-even n (cons a x) = cons (add1 a) (cong x add1)

data Either (A : U) (B : U) : U where
  left : A -> Either A B
  right : B -> Either A B

ind-Either : {A B : U}
           -> (motive : Either A B -> U)
           -> (target : Either A B)
           -> (basel : (a : A) -> motive (left a))
           -> (baser : (b : B) -> motive (right b))
           -> (motive target)
ind-Either m (left x) bl br = bl x
ind-Either m (right x) bl br = br x

odd-or-even : (n : Nat) -> Either (Odd n) (Even n)
odd-or-even n = ind-Nat (λ k → Either (Odd k) (Even k)) n
  (right (cons zero (same zero)))
  λ n-1 IH →
    ind-Either (λ _ → Either (Odd (add1 n-1)) (Even (add1 n-1))) IH
      (λ a → right (add1-odd-even n-1 a))
      (λ b → left (add1-even-odd n-1 b))

data Absurd : U where

ind-Absurd : (motive : Absurd -> U)
           -> (target : Absurd)
           -> motive target
ind-Absurd motive ()

Not : U -> U
Not X = X -> Absurd

zero-not-odd : Not (Odd zero)
zero-not-odd (cons a ())
