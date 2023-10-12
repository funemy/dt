#lang scribble/text

Quiz 4: https://www.gradescope.ca/courses/11611/assignments/59446

1. What is the type, in Pie's syntax, of the generic recursive eliminator for lists? (Use `Pi` only to introduce type variables, and `->` for any other function. Use multi-argument functions rather than explicit currying.)

(Pi ((E U) (X U)) (-> (List E) X (-> E (List E) X X) X))

2. A List is built either of the empty list, or the constructor `::` which adds one element to a list.

   The function `length` takes a List of Atoms and returns a natural number
   representing the number of elements in the list. When implementing `length` in
   using the recursive eliminator, what is the type of the function that handles
   recursively eliminating `::`?

(-> Atom (List Atom) Nat Nat)

3.1 What is the return type of `head`, the total function that takes a List of `E` and returns the first element of that List?
    ( ) `E`
    ( ) `List E`
    ( ) `Atom`
    (X) None of the above

3.2 Why?
    Using the recursive eliminator, we would define head as something like:
    rec-List : (Pi ((E U) (X U)) (-> (List E) X (-> E (List E) X X) X))

     head E ls = rec-List E E ls ?? (lambda (e ls x) ??)

     But there is no element of E to return in the case for nil.
