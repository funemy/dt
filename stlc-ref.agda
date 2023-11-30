open import Data.Fin hiding (_+_)
open import Data.Nat
open import Data.Vec
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Data.Unit
open import Data.String
open import Relation.Binary.PropositionalEquality

-- ignore me, working around namespaces
_ = Set

module inductive-sums-of-products where
  data Expr : Set where
    var : ∀ {n} -> Fin n -> Expr
    lambda : Expr -> Expr
    app : Expr -> Expr -> Expr
    nlit : ℕ -> Expr
    nadd : Expr -> Expr -> Expr
{-
   Roughly, this defines the following type:

   Expr = Either (Σ (x : (Atom × (Fin n))) (≡ (Atom × (Fin n)) (cons 'var (cdr x))))
                 (Σ (x : (Atom × Expr)) (≡ (Atom × Expr) (cons 'lambda (cdr x))))
                 (Σ (x : (Atom × Expr × Expr)) (≡ (Atom × Expr × Expr) (cons 'app (car (cdr x)) (cdr (cdr x)))))
                 (Σ (x : (Atom × ℕ)) (≡ (Atom × ℕ) (cons 'nlit (cdr x))))
                 (Σ (x : (Atom × Expr × Expr)) (≡ (Atom × Expr × Expr) (cons 'nadd (car (cdr x)) (car (cdr x)))))

   then defines a nice induction principle for this type.

   Actually, let's see if we can define that type ourselves, just with the
   primitives of Pie.
   We'll need a trick to make it work.

   We'll also define just the arithmetic subset, for simplicity

   Expr = Either (Σ (x : (Atom × ℕ)) (≡ (Atom × ℕ) x (cons 'nlit (cdr x))))
                 (Σ (x : (Atom × Expr × Expr)) (≡ (Atom × Expr × Expr) x (cons 'nlit (car (cdr x)) (cdr (cdr x)))))
-}


Either : Set -> Set -> Set
Either A B = A ⊎ B

left : ∀ {A B} -> A -> Either A B
left a = inj₁ a

right : ∀ {A B} -> B -> Either A B
right a = inj₂ a

Absurd = ⊥

Trivial = ⊤
sole = tt

Atom = String

cons : ∀ {A : Set} {B : A -> Set} -> (a : A) -> (B a) -> Σ A B
cons e1 e2 = e1 , e2

car : ∀ {A : Set} {B : A -> Set} -> Σ A B -> A
car (e1 , e2) = e1

cdr : ∀ {A : Set} {B : A -> Set} -> (p : Σ A B) -> B (car p)
cdr (e1 , e2) = e2

Expr' : ℕ -> Set
Expr' 0 = Absurd
Expr' (suc n) = Either (Σ (Atom × ℕ) (λ x -> x ≡ (cons "nlit" (cdr x))))
                       (Σ (Atom × (Expr' n) × (Expr' n)) (λ x -> x ≡ (cons "nadd" (cons (car (cdr x)) (cdr (cdr x))))))


-- 5 is an Expr'
5-expr : Expr' 1
5-expr = left (cons (cons "nlit" 5) refl)

-- nadd 5 5 is an Expr, since 5 is an Expr
_ : Expr' 2
_ = (right (cons (cons "nadd" (cons 5-expr 5-expr))
                 refl))

-- Let's implement the induction principle for Expr'
ind-Expr' : ∀ {n : ℕ} -> (target : Expr' n) ->
            (motive : (n : ℕ) -> (Expr' n) -> Set) ->
            (nlit-case : (m : ℕ) -> (n : ℕ) -> (motive (suc m) (left (cons (cons "nlit" n) refl)))) ->
            (nadd-case : (m : ℕ) -> ((e1 : Expr' m) -> (e2 : Expr' m) ->
              (ih1 : (motive m e1)) ->
              (ih2 : (motive m e2)) ->
              (motive (suc m) (right (cons (cons "nadd" (cons e1 e2)) refl))))) ->
            (motive n target)
ind-Expr' {0} () motive nlit-case nadd-case
ind-Expr' {suc m} (inj₁ ((."nlit" , n) , refl)) motive nlit-case nadd-case =
  (nlit-case m n)
ind-Expr' {suc m} (inj₂ ((."nadd" , e1 , e2) , refl)) motive nlit-case nadd-case =
  (nadd-case m e1 e2 (ind-Expr' e1 motive nlit-case nadd-case)
                     (ind-Expr' e2 motive nlit-case nadd-case))

{-
   We could compile the above into ind-Nat, ind-Absurd, ind-Either, replace,
   car, and cdr.
   It would be very verbose.

   Agda, instead, has an abstraction that asks essentially: if it were safe to
   compile into dependent elimination, don't bother, and instead do dependent
   pattern matching and substitute in the type directly.
-}

{-
   The data form capture this pattern.
   It defines a recursive sum of products.

   1. Recursive: inductively defined, like over natural numbers, but intrinsically
      so: capturing that thing that makes natural numbers themselves inductively
      defined.

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

      Some of you manually implemented this pattern in the homeworks: add1 in
      Pie is not a function, but you often want to use it as a function.
-}

{-
Okay, let's go back to our definition of Expr:

data Expr : Set where
  var : ∀ {n} -> Fin n -> Expr
  lambda : Expr -> Expr
  app : Expr -> Expr -> Expr
  nlit : ℕ -> Expr
  nadd : Expr -> Expr -> Expr


Let's suppose we'd like to write a type checker for this language (and maybe
eventually an evaluator), and prove that type checking is decidable.

How do we do that?

Couple ways:
- An well-typed inductive encoding, such that if type checking in Agda is
  decidable, so is type checking our terms.
- A raw syntax + typing derivation, where we prove there is an algorithm to
  construct a derivation from syntax.
- A codata specification (theory) + an implementation (model).
-}

module well-typed-syntax where
  data Type : Set where
    `Nat : Type
    `Fun : Type -> Type -> Type

  -- The well-typed inductive encoding.
  -- If inference of the index is always decidable, then syntax-directed type checking is decidable.
  data TExpr : Type -> Set where
    tvar : ∀ {n} ->
      Fin n ->
      -----------------
      TExpr `Nat

    tlambda : ∀ {A B} ->
      TExpr A ->
      ---------------
      TExpr (`Fun A B)

    tapp : ∀ {A B} ->
      TExpr (`Fun A B) ->
      TExpr A ->
      ------
      TExpr B

    tnlit :
      ℕ ->
      ----
      TExpr `Nat

    tnadd :
      TExpr `Nat ->
      TExpr `Nat ->
      -----
      TExpr `Nat

  _ : TExpr `Nat
  _ = tnadd (tnlit 5) (tnlit 5)

  -- Not a very compelling proof, but might be good enough for your purposes.
  -- Unfortunately, I don't think inference os the index *is* decidable. So
  -- probably not good enough if you want a proof, but might be good enough if you
  -- want to prove other things.

module raw-synatx where
  data Type : Set where
    `Nat : Type
    `Fun : Type -> Type -> Type

  data Expr : ℕ -> Set where
    var : ∀ {n} -> Fin n -> Expr n
    lambda : ∀ {n} -> Expr (suc n) -> Expr n
    app : ∀ {n} -> Expr n -> Expr n -> Expr n
    nlit : ∀ {n} -> ℕ -> Expr n
    nadd : ∀ {n} -> Expr n -> Expr n -> Expr n


  Env = Vec Type

  data _⊢_∈_ : ∀ {n} -> Env n -> Expr n -> Type -> Set where
    Var : ∀ {n A} ->
      {Γ : Env n} ->
      (m : Fin n) ->
      A ≡ (lookup Γ m) ->
      ----------
      Γ ⊢ var m ∈ A


    NLit-I : ∀ {m} {Γ : Env m} {n} ->
      -----------------
      Γ ⊢ nlit n ∈ `Nat

    NAdd-E : ∀ {m} {Γ : Env m} {e1 e2} ->
      Γ ⊢ e1 ∈ `Nat ->
      Γ ⊢ e2 ∈ `Nat ->
      -----------------
      Γ ⊢ nadd e1 e2 ∈ `Nat


    Fun-I : ∀ {m} {Γ : Env m} {e A B} ->
      (A ∷ Γ) ⊢ e ∈ B ->
      -----------------
      Γ ⊢ lambda e ∈ `Fun A B

    Fun-E : ∀ {m} {Γ : Env m} {e1 e2 A B} ->
      Γ ⊢ e1 ∈ `Fun A B ->
      Γ ⊢ e2 ∈ A ->
      -----------------
      Γ ⊢ app e1 e2 ∈ B

  Not : Set -> Set
  Not A = A -> Absurd

  Dec : Set -> Set
  Dec A = Either A (Not A)

  type-checking-dec : ∀ {n} (Γ : Env n) (e : Expr n) -> Dec (Σ Type λ A -> (Γ ⊢ e ∈ A))
  type-checking-dec Γ (var x) = left (cons (lookup Γ x) (Var x refl))
  type-checking-dec Γ (lambda e) = {!!}
  type-checking-dec Γ (app e e₁) = {!!}
  type-checking-dec Γ (nlit x) = (left (cons `Nat NLit-I))
  -- the with construct lets me introduce nested pattern matching.
  type-checking-dec Γ (nadd e1 e2) with (type-checking-dec Γ e1) | (type-checking-dec Γ e2)
  ... | inj₁ (`Nat , De1) | inj₁ (`Nat , De2) = (left (cons `Nat (NAdd-E De1 De2)))
  ... | De1 | De2 = {!!} -- There are going to be a lot of cases here if we proceed.
