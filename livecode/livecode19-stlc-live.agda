
-- Expr is one of:
-- - (cons 'nlit n)
-- - (cons 'lambda e), where e is an Expr
-- - (cons 'app e1 e2), where ei is an Expr

open import Data.Nat

Nat = ℕ

-- data Expr : Set where
--   nlit : Nat -> Expr
--   lambda : Expr -> Expr
--   app : Expr -> Expr -> Expr

{-

Expr = Either (Σ (e : (Atom × Nat)) (≡ (Atom × Nat) e (cons 'nlit (cdr x))))
              (Σ (e : (Atom × Expr)) (≡ (Atom × Expr) e (cons 'lambda (cdr x))))
              (Σ (e : (Atom × Expr × Expr)) (≡ (Atom × Expr × Expr)
                                               e
                                               (cons 'app (car (cdr x)) (cdr (cdr x)))))
-}

open import Data.Sum
open import Data.Product
open import Data.Empty
open import Data.String
open import Relation.Binary.PropositionalEquality

Atom = String

Absurd = ⊥

Either : Set -> Set -> Set
Either A B = A ⊎ B

cdr = proj₂
car = proj₁

Expr' : Nat -> Set
Expr' 0 = Absurd
Expr' (suc n) = Either (Σ (Atom × Nat) (λ e -> (e ≡ ("nlit" , (cdr e)))))
                       (Either
                         (Σ (Atom × (Expr' n)) (λ e -> (e ≡ ("lambda" , (cdr e)))))
                         (Σ (Atom × (Expr' n) × (Expr' n))
                           (λ e -> (e ≡ ("app" , (car (cdr e)) , (cdr (cdr e)))))))

-- data Expr : Set where
--   nlit : Nat -> Expr
--   lambda : Expr -> Expr
--   app : Expr -> Expr -> Expr

data Expr'' : Set where
  nlit : Nat -> Expr''
  lambda : (Expr'' -> Expr'') -> Expr''
  app : Expr'' -> Expr'' -> Expr''


{-
Recursive sum of products.

1. Recursive: inductively defined, like over natural numbers, but intrinsically so: capturing that thing that makes natural numbers themselves inductively defined.

2. Sum: each constructor represents something you can (dependently) case
   split on.

   `Either` is the primitive sum, but `data` generalize this: there
   can be more cases than just left and right.

3. Products: Each constuctor takes a dependent linked list of arguments.

   There's another layer of abstraction on top of this product.
   We specify the constructor with a function type, but that is syntactic
   sugar, allowing you to use the constructor both as a function, and curry
   the application of its arguments, until it is fully applied.
   The fully applied version of the constructor is the value form.
   Conceptually, you should think of this as defining two names: the name of
   the function that builds the value, and a separate name of the fully
   applied value.
-}

left = inj₁

cons : ∀ {A B} -> (a : A) -> (B a) -> Σ A B
cons e1 e2 = e1 , e2

-- ind-Expr' : ∀ {n} -> (target : Expr' n)
--             (motive : (m : Nat) -> (Expr' m) -> Set)
--             (nlit-case : (m : Nat) -> (n : Nat) -> (motive m (left (cons (cons "nlit" n) refl)))) ->
--             (lambda-case : ?) ->
--             (app-case : ?) ->
--             (motive n target)

--

module raw where
  data Expr : Set where
    nlit : Nat -> Expr
    lambda : Expr -> Expr
    app : Expr -> Expr -> Expr

  -- can't use this type:
  -- eval : Expr -> Value
  Value : Set
  eval : Expr -> Either String Value

  module example where
    _ : Expr
    _ = nlit 0

    _ : Expr
    _ = app (nlit 0) (nlit 0)

module intrisic where
  data Type : Set where
    `Nat : Type
    `Fun : Type -> Type -> Type

  Value : Type -> Set
  Value `Nat = ℕ
  Value (`Fun A B) = (Value A) -> (Value B)

  data Expr : Type -> Set where
    nlit :
      Nat ->
      ---------
      Expr `Nat

    nadd :
      Expr `Nat ->
      Expr `Nat ->
      ------------
      Expr `Nat

    lambda : ∀ {B} -> (A : Type) ->
      ((Value A) -> Expr B) ->
      ---------------
      Expr (`Fun A B)

    app : ∀ {A B} ->
      Expr (`Fun A B) ->
      Expr A ->
      ----
      Expr B

  module examples where
    _ : Expr `Nat
    _ = (nlit 0)

    -- _ : Expr (`Fun `Nat `Nat)
    -- _ = (nlit 0)

    -- _ : Expr `Nat
    -- _ = (app (nlit 0) (nlit 0))

  open import Data.Vec

  -- data Value : Set where
  --   vnat : Nat -> Value
  --   clos : ∀ {n B} -> (Vec Value n) -> Expr B -> Value


  eval : ∀ {A} -> Expr A -> (Value A)
  eval (nlit x) = x
  eval (nadd e1 e2) = (eval e1) + (eval e2)
  eval (lambda A e) = (λ a -> (eval (e a)))
  eval (app e1 e2) = (eval e1) (eval e2)

  _ : Expr (`Fun `Nat `Nat)
  _ = lambda `Nat (λ x -> nlit x)

  _ : Expr `Nat
  _ = app (lambda `Nat (λ x -> nlit x)) (nlit 0)


module A where

  data Type : Set where
    `Nat : Type
    `Fun : Type -> Type -> Type

  open import Data.Fin

  data Expr : Set where
    var : ∀ {n} -> (Fin n) -> Expr
    nlit : Nat -> Expr
    lambda : Type -> Expr -> Expr
    app : Expr -> Expr -> Expr

  open import Data.Vec

  Env = Vec Type

  _ : Expr
  _ = lambda `Nat (var (fromℕ 0))

  -- \vdash \in

  data _⊢_∈_ : ∀ {n} -> Env n -> Expr -> Type -> Set where
    Var : ∀ {n A} ->
      (Γ : Env n) ->
      (x : Fin n) ->
      A ≡ (lookup Γ x) ->
      ---------------
      Γ ⊢ (var x) ∈ A

    NLit-I : ∀ {m n} {Γ : Env m} ->
      -------
      Γ ⊢ (nlit n) ∈ `Nat

  _ : [] ⊢ (nlit 0) ∈ `Nat
  _ = NLit-I

  Dec : Set -> Set
  Dec A = Either A (A -> ⊥)

  type-infer-dec : {n : Nat} (Γ : Env n) (e : Expr) ->
                   Dec (Σ Type (λ A -> (Γ ⊢ e ∈ A)))
  type-infer-dec Γ (var x) = {!!} -- inj₁ ((lookup Γ ?) , (Var Γ x refl))
  type-infer-dec Γ (nlit x) = inj₁ (`Nat , NLit-I)
  type-infer-dec Γ (lambda x e) = inj₂ λ ()
  type-infer-dec Γ (app e e₁) = inj₂ λ ()
