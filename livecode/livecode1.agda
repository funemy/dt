open import Data.Nat
open import Data.Bool

Nat = ℕ

x : Nat
x = 5

-- y : Nat
-- y = true

open import Data.Product

pairofnat : Set
pairofnat = Nat × Nat

illtyped : Set
illtyped = Set
