#lang scribble/text

Quiz:
https://www.gradescope.ca/courses/11611/assignments/60584/

1. What is the type of the motive for the following type `A` with two constructors `c1` and `c2`?
`A : U`
`c1 : A`
`c2 : A`

(Pi ((X : U)) (-> X X X))?? this would be the type of rec-A, or similar
(-> A U) ? this is the type of the motive

2. What is the type of the motive for the following type?
`B : U`
`c3 : (-> A B)`
`c4 : (-> A (-> B B))`

(-> B U)

3. What are the types of the methods for `B`?

1. (Pi ((a A)) (motive (c3 a))
2. (Pi ((a A) (b B)) (-> (motive b) (motive (c4 a b))))

4. What is the type of the motive for the following type?
`C : (-> B U)`
`c5 : C (c3 c1)`
`c6 : (Pi ((b : B)) (-> A (C b)))`

(Pi ((b B)) (-> (C b) U))



















