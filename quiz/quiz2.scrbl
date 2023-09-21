#lang scribble/text

Quiz:
https://www.gradescope.ca/courses/11611/assignments/54406/

1. What judgments are true of (Pair U U)?
   - (Pair U U) is a Type
   - (Pair U U) is the same Type as (Pair U U)
   - (Pair U U) is the same Type as (car (cons (Pair U U) Nat)) ??
   - It's NOT the case that (Pair U U) is a U
2. Is (add1 (+ 1 z)) a value?
   - YES! if we have a constructor at the top, it's a value
3. Is (add1 (+ 1 z)) a normal form?
   - NO, there's a more direct way to write this expression: (add1 (add1 z))
4. Is (+ 1 z) a:
   1. value
   2. normal form
   3. expression
   4. type
5. What is the normal form of (iter-Nat (add1 z) (add1 z) (lambda (x) (add1 x)))
   - (the Nat (add1 (add1 z)))