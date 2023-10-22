#lang scribble/text

*It's time for: William's Tricky Questions!*

Quiz: https://www.gradescope.ca/courses/11611/assignments/60976

1. Does there exist a term of type `(≡ Nat (+ x y) (+ x y))`?

Yes!

2. Is `(+ x y)` the same `Nat` `(+ x y)`?

Yes!

3. Does there exist a term of type `(≡ Nat (+ x y) (+ y x))`?

Yes?
3a: Does there exist a term of type
    `(Pi ((x Nat) (y Nat))) (≡ Nat (+ x y) (+ y x))`?

Yes!

4. Is `(+ x y)` the same `Nat` as `(+ y x)`?

No!

5. Is `(same (+ x y))` a `(≡ Nat (+ x y) (+ y x))`?

No.

6. Is `(same (+ x y))` a `(≡ Nat (+ x y) (+ x y))`?

Yes
