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

data ≡ (X : U) : (from : X) → (to : X) → U where
  same : (the : X) → (≡ X the the)

test1 : Σ Nat (λ n -> (≡ Nat n one))
test1 = cons one (same one)

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
