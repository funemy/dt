#lang scribble/text

Quiz: https://www.gradescope.ca/courses/11611/assignments/55462

1. How many judgments does our in-class formalization of Pie have?
   - infinite
   - 4: Something has a type, something is a type, two things are the same at a type, and two types are the same
   - maybe 5.
   - maybe William is using "judgment" wrong
2. What typing rule causes typing to depend on type equivalence (sameness)? (Enter your answer in all lower case.)
   - Conv
   - Two variants of the rule: one with sameness, one with reduction
     - they're related; we'll see how
3. Why does type equivalence requires deciding term equivalence (sameness)?
   - "large elimination".
   - our language allows computing a type by eliminating a term.
4. Which natural eliminator is the most expressive?
   (a) which-Nat
   (b) iter-Nat
   (c) rec-Nat <- the one with the most parameters?
   (d) add1
   (e) z
   (f) U
5. What is the eliminator for `U`?
   - (the A e) if A : U
   - (Pi ((x A)) B)
   - Universes a la Russell; this eliminator is a little... handy wavy.
   - With Universes a la Tarski, there is an explicit eliminator.
