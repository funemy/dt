module Lec19-stlc where

open import Data.Nat

module raw-syntax where
  open import Data.Fin
  open import Data.Vec
  open import Relation.Binary.PropositionalEquality

  data Expr : Set where
    var : ∀ {n} → Fin n → Expr
    nlit : ℕ → Expr
    lambda : Expr → Expr
    app : Expr → Expr → Expr

  data Type : Set where
    `Nat : Type
    `Fun : Type → Type → Type

  Env = Vec Type

  data _⊢_∈_ : ∀ {n} → Env n → Expr → Type → Set where
    Var : ∀ {n} {A : Type} →
      (Γ : Env n) →
      (x : Fin n) →
      A ≡ (lookup Γ x) →
    -------------------------------
      Γ ⊢ (var x) ∈ A

    NLit-I : ∀ {m n} {Γ : Env m} →
    -------------------------------
      Γ ⊢ (nlit n) ∈ `Nat

  _ : [] ⊢ (nlit 0) ∈ `Nat
  _ = NLit-I

  open import Data.Sum
  open import Data.Empty
  open import Data.Product
  open import Relation.Nullary as R hiding (Dec)
  open import Data.Nat.Properties using (≤-reflexive)

  Either : Set → Set → Set
  Either A B = A ⊎ B

  Dec : Set → Set
  Dec A = Either A (A → ⊥)

  type-checking-dec : ∀ {n} → (Γ : Env n) → (e : Expr) → Dec (Σ Type (λ A → (Γ ⊢ e ∈ A)))
  type-checking-dec Γ (var x) = inj₁ ((lookup Γ {!x!}) , {!!})
  -- if the env is empty, then false
  -- type-checking-dec {.zero} [] (var x) = inj₂ λ { (fst , Var .[] () x₁)}
  -- -- if the env is non-empty
  -- type-checking-dec {suc n} (v ∷ Γ) (var {nx@(suc nx')} x) with nx Data.Nat.≤? suc n
  -- ... | yes p@(s≤s p') = inj₁ (lookup (v ∷ Γ) (inject≤ x p) , Var (v ∷ Γ) (inject≤ x p) refl)-- {!!})
  -- ... | no ¬p = inj₂ λ { (fst , Var .(v ∷ Γ) y x) → ¬p (≤-reflexive refl)}
  type-checking-dec Γ (nlit x) = inj₁ (`Nat , NLit-I)
  type-checking-dec Γ (lambda e) = inj₂ λ ()
  type-checking-dec Γ (app e e₁) = inj₂ λ ()


{-
The definition above can be thought of the definition below:

Expr = Either
       Σ (e : Atom × Nat) (≡ (Atom × ℕ) e (cons 'nlit (cdr x)))
       Σ (e : Atom × Expr) (≡ (Atom × Expr) e (cons 'lambda (cdr x)))
       Σ (e : Atom × Expr × Expr) (≡ (Atom × Expr × Expr) e (cons 'lambda (car (cdr x)) (cdr (cdr x))))
-}

open import Data.Sum
open import Data.Product
open import Data.Empty
open import Data.String
open import Relation.Binary.PropositionalEquality

Absurd = ⊥

Atom = String

Either : Set → Set → Set
Either A B = A ⊎ B

cdr = proj₂
car = proj₁


module intrinsic where
  data Type : Set where
    `Nat : Type
    `Fun : Type → Type → Type

  open import Data.Vec

  Value : Type → Set
  Value `Nat = ℕ
  Value (`Fun A B) = Value A → Value B


  data Expr : Type → Set where
    nlit : ℕ → Expr `Nat
    nadd : Expr `Nat → Expr `Nat → Expr `Nat
    lambda : ∀ {B : Type} → (A : Type) → (Value A → Expr B) → Expr (`Fun A B)
    app : ∀ {A B} → Expr (`Fun A B) → Expr A → Expr B

  eval : ∀ {A} → Expr A → Value A
  eval (nlit x) = x
  eval (nadd n m) = eval n + eval m
  eval (lambda A e) = λ a → eval (e a)
  eval (app f a) = eval f (eval a)

  _ : Expr (`Fun `Nat `Nat)
  _ = lambda `Nat (λ x → nlit x)

  _ : Value `Nat
  _ = eval (app (lambda `Nat (λ x → nlit x)) (nlit 2))

  _ : eval (app (lambda `Nat (λ x → nlit x)) (nlit 2)) ≡ 2
  _ = refl



