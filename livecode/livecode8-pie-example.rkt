#lang pie

(claim step-peas
  (Π ((n-1 Nat))
    (→ (Vec Atom n-1)
      (Vec Atom
        (add1 n-1)))))
(define step-peas (lambda (n-1 vn-1) (vec:: 'ADAM vn-1)))

(claim peas (Pi ((n Nat)) (Vec Atom n)))
(define peas (lambda (n) (ind-Nat n (lambda (v) (Vec Atom v)) vecnil step-peas)))