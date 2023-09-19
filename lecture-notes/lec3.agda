data Nat : Set where
  z : Nat
  add1 : Nat -> Nat

U = Set
which-Nat : ∀ {X : U} -> Nat -> X -> (Nat -> X) -> X
which-Nat z b s = b
which-Nat (add1 n) b s =  s n

iter-Nat : ∀ {X : U} -> Nat -> X -> (X -> X) -> X
iter-Nat z b s = b
iter-Nat (add1 n) b s = s (iter-Nat n b s)

rec-Nat : ∀ {X : U} -> Nat -> X -> (Nat -> X -> X) -> X
rec-Nat z b s = b
rec-Nat (add1 n) b s = s n (rec-Nat n b s)
