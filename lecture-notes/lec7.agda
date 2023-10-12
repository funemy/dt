U = Set

data List (E : U) : U where
  nil : List E
  lcons : E -> List E -> List E

rec-List : ∀ {E X : U} -> List E -> X -> (E -> (List E) -> X -> X) -> X
rec-List nil base step = base
rec-List (lcons x l) base step = step x l (rec-List l base step)

-- Cannot define head for List E
-- head : ∀ {E} -> List E -> E
-- head = {!!}

data Nat : U where
  zero : Nat
  suc : Nat -> Nat

data Vec (E : U) : Nat -> U where
  vnil : Vec E zero
  vcons : {n : Nat} -> E -> Vec E n -> Vec E (suc n)

head' : ∀ {E : U} -> {k : Nat} -> Vec E (suc k) -> E
head' (vcons x v) = x

open import Data.String

ind-Nat : (motive : Nat -> U)
          -> (target : Nat)
          -> motive zero
          -> ((k : Nat) -> motive k -> motive (suc k))
          -> motive target
ind-Nat f zero base step = base
ind-Nat f (suc n) base step = step n (ind-Nat f n base step)

foo : (n : Nat) -> Vec String n
foo n = ind-Nat (λ k -> Vec String k) n vnil λ _ v -> vcons "foo" v

ind-vec : ∀ {E : U} -> {n : Nat}
          -> (motive : ((k : Nat) -> Vec E k -> U))
          -> (target : Vec E n)
          -> (motive zero vnil)
          -> ((k : Nat) -> (hd : E) -> (v : Vec E k) -> motive k v -> motive (suc k) (vcons hd v))
          -> motive n target
ind-vec f vnil base step = base
ind-vec {_} {suc n} f (vcons x v) base step = step n x v (ind-vec f v base step)

-- left as an exercise :)
vec->list : ∀ {E : U} -> (n : Nat) -> Vec E n -> List E
vec->list n v = {!!}
