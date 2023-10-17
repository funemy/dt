U = Set

module quiz where
  data A : U where
    c1 : A
    c2 : A

  data B : U where
    c3 : A -> B
    c4 : A -> B -> B

  data C : B -> U where
    c5 : C (c3 c1)
    c6 : (b : B) -> A -> C b

  ind-C : (motive : ((b : B) -> C b -> U)) -> (b : B) -> (target : C b) ->
          (motive (c3 c1) c5) ->
          ((b : B) -> (a : A) -> (motive b (c6 b a))) ->
          (motive b target)
  ind-C motive .(c3 c1) c5 m1 m2 = m1
  ind-C motive b (c6 .b x) m1 m2 = m2 b x

module complex-dependent-elimination where
  -- Here, we need more universes than Pie has. Review page 357 for some
  -- pointers on this topic.
  data A {l} : Set l where
    c1 : A
    c2 : A

  ind-A : ∀ {l} -> (motive : A -> Set l) -> (target : A) -> (motive c1) -> (motive c2) -> motive target
  ind-A motive c1 m1 m2 = m1
  ind-A motive c2 m1 m2 = m2

  data Nat : Set where
    zero : Nat

  data Atom : Set where
    foo : Atom

  -- A is another name for Booleans
  if-then-else = ind-A
  Bool = A
  true = c1
  false = c2

  -- test has all the following types
  -- test : ((λ c -> if-then-else (λ _ -> Set) c Nat Atom) true)
  -- test : (if-then-else (λ _ -> Set) true Nat Atom)
  test : Nat
  test = if-then-else (λ c -> if-then-else (λ _ -> Set) c Nat Atom) true zero foo
