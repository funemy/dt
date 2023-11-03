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

+ : Nat -> Nat -> Nat
+ n m = ind-Nat (λ i -> Nat) n m (λ _ acc -> (add1 acc))

one = add1 zero
two = add1 one
three = add1 two
four = add1 three
five = add1 four

--------------------------------------------------------------------------

module SimplePair where
  data Pair (A : U) (B : U) : U where
    cons : (a : A) -> B -> Pair A B

  car : ∀ {A B}  -> Pair A B -> A
  car (cons x x₁) = x

  cdr : ∀ {A B} -> (p : Pair A B) -> B
  cdr (cons x x₁) = x₁

--------------------------------------------------------------------------

-- Dependent Pair
data Σ (A : U) (B : A -> U) : U where
  cons : (a : A) -> (B a) -> Σ A B

car : ∀ {A B}  -> Σ A B -> A
car (cons x x₁) = x

cdr : ∀ {A B} -> (p : Σ A B) -> (B (car p))
cdr (cons x x₁) = x₁

data ≡ (X : U) : (from : X) -> (to : X) -> U where
  same : (the : X) -> (≡ X the the)

test1 : Σ Nat (λ x -> (≡ Nat x one))
-- Σ x:Nat.(≡ Nat x one)
-- test1 = cons one (same one)
test1 = cons one (same one)

-- Σ x:??. x ∈ Nat

-- test' : Σ U (λ x -> (≡ U ? ?))

--------------------------------------------------------------------------

data List (A : U) : U where
  listnil : List A
  listcons : A -> (List A) -> List A

rec-List : {A : U} -> {X : U} ->
           (target : (List A)) -> (base : X) ->
           (step : A -> (List A) -> X -> X) ->
           X
rec-List listnil base step = base
rec-List (listcons x target) base step = step x target (rec-List target base step)

--------------------------------------------------------------------------

data Vec (A : U) : Nat -> U where
  vecnil : Vec A zero
  veccons : (n : Nat) -> A -> Vec A n -> Vec A (add1 n)

--------------------------------------------------------------------------

list->vec' : {E : U} -> (List E) -> (Σ Nat (λ l -> (Vec E l)))
list->vec' es = cons zero vecnil

length : {E : U} -> (List E) -> Nat
length es = rec-List es zero λ head tail acc → (add1 acc)

ind-List : {E : U} -> (target : List E) ->
           (motive : (List E) -> U) ->
           (base : (motive listnil)) ->
           (step : (e : E) -> (tail : List E) -> (motive tail) -> (motive (listcons e tail))) ->
           (motive target)
ind-List listnil motive base step = base
ind-List (listcons x target) motive base step = step x target (ind-List target motive base step)

list->vec'' : {E : U} -> (es : (List E)) -> (Vec E (length es))
list->vec'' {E} es = ind-List es (λ es → (Vec E (length es))) vecnil
  λ e tail v → veccons (length tail) e v

-- the autocompleted def
-- list->vec'' {E} es = ind-List es (λ es → (Vec E (length es))) vecnil
--   λ e tail → veccons (rec-List tail zero (λ _ _ → add1)) e

-- vec->list : {E : U} {l : Nat} -> (Vec E l) -> (List E)
-- vec->list v = listnil
--
-- list->vec-the-perfect : {E : U} -> (e : (List E)) ->
--               (Σ Nat (λ l -> (Σ (Vec E l) (λ v -> (≡ (List E) e (vec->list v))))))
-- list->vec-the-perfect e = cons zero (cons vecnil {!!})

import Data.Product
