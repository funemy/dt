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


ind-Nat : (motive : Nat -> U)
          -> (target : Nat)
          -> motive zero
          -> ((k : Nat) -> motive k -> motive (suc k))
          -> motive target
ind-Nat f zero base step = base
ind-Nat f (suc n) base step = step n (ind-Nat f n base step)

module Example where
  open import Data.String
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
vec->list n v = nil

head : {A : U} -> {n : Nat} -> Vec A (suc n) -> A
head (vcons x v) = x

tail : {A : U} -> {n : Nat} -> Vec A (suc n) -> Vec A n
tail (vcons x v) = v

plus : Nat -> Nat -> Nat
plus n m = ind-Nat (λ k -> Nat) n m λ _ prev -> (suc prev)

data ≡ {A : U} : (from : A) -> (to : A) -> Set where
  same : (the : A) -> (≡ the the)

-- the type of ind-eq is more expressive than subst
-- notice when we are defining subst, the λ only used `x` but not `eq`
ind-eq : {A : U} -> {from to : A}
         -> (motive : {x : A} -> (≡ from x) -> U)
         -> (target : ≡ from to)
         -> (motive (same from))
         -> (motive target)
ind-eq f (same _) base = base

subst : {A : U} -> {from to : A} -> (motive : A -> U) -> (target : ≡ from to) -> (motive from) -> (motive to)
subst f t px = ind-eq (λ {x} eq -> f x) t px

cong : {A B : U} -> {x y : A} -> (≡ x y) -> (f : A -> B) -> (≡ (f x) (f y))
cong {_} {_} {x} {y} eq f = subst (λ k -> ≡ (f x) (f k)) eq (same (f x))

trans : {A : U} -> {x y z : A} -> ≡ x y -> ≡ y z -> ≡ x z
trans {_} {x} {_} {_} ≡xy ≡yz = subst (λ k -> ≡ x k) ≡yz ≡xy

sym : {A : U} -> {x y : A} -> ≡ x y -> ≡ y x
sym {_} {x} {_} ≡xy = subst (λ k -> ≡ k x) ≡xy (same x)

-- TODO: is it possible to use ind-eq to prove uip?

uip : {A : U} -> {x y : A} -> (g : ≡ x y) -> (h : ≡ x y) -> ≡ g h
uip {_} {x} {y} g h = {!!}

uip' : {A : U} -> {x y : A} -> (g : ≡ x y) -> (h : ≡ x y) -> ≡ g h
uip' {_} {x} {_} (same _) (same _) = same (same x)

one : Nat
one = suc zero

-- this is special
-- in general we cannot prove function equality without fuction extensionality
+1=suc : ≡ (plus one) (suc)
+1=suc = same suc

plus-suc-l : (n m : Nat) -> ≡ (plus (suc n) m) (suc (plus n m))
plus-suc-l n m = same (suc (ind-Nat (λ _ → Nat) n m (λ k → suc)))

plus-suc-r : (n m : Nat) -> ≡ (plus n (suc m)) (suc (plus n m))
plus-suc-r n m = ind-Nat (λ k -> ≡ (plus k (suc m)) (suc (plus k m))) n (same (suc m)) (λ k ih -> cong ih suc)

lemma1 : (m : Nat) -> ≡ (plus zero m) (plus m zero)
lemma1 m = ind-Nat (λ k -> ≡ (plus zero k) (plus k zero)) m (same zero) (λ k p -> trans (plus-suc-r zero k) (trans (cong p suc) (sym (plus-suc-l k zero))))

lemma2 : (k n : Nat) -> ≡ (plus n k) (plus k n) -> ≡ (plus n (suc k)) (plus (suc k) n)
lemma2 k n ih = helper (cong ih suc)
   where
     helper : ≡ (suc (plus n k)) (suc (plus k n)) -> ≡ (plus n (suc k)) (plus (suc k) n)
     helper p = trans (plus-suc-r n k) (trans (cong ih suc) (sym (plus-suc-l k n)))

plus-comm : (n m : Nat) -> (≡ (plus n m) (plus m n))
plus-comm n m = ind-Nat (λ k -> (≡ (plus n k) (plus k n))) m (sym (lemma1 n)) (λ k p -> lemma2 k n p)



