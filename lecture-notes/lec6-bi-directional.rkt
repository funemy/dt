#lang racket

;; A Variable is a symbol

;; An Expr is one of:
;; - an natural number literal
;; - `(+ ,e1 ,e2) where e1 is an Expr, and e2 is an Expr
;; - a string literal
;; - `(the ,A ,e) where A is a Type and e is an Expr
;; - a Variable
;; - `(let ([,x ,e1]) ,e2) where x is a Variable, and e1 and e2 are Exprs
;; - `(lambda (,x) ,e) where x is a Variable an e is an Expr
;; - `(,e1 ,e2) where e1 and e2 are Exprs


;; A Type is one of:
;; - 'Nat
;; - 'String
;; - `(-> ,A ,B) where A and B are types


;; Takes an Expr and returns a Type or #f representing failure
(define (type-synth env e)
  (match e
    [`(+ ,e1 ,e2)
     (and (type-check env e1 'Nat)
          (type-check env e2 'Nat)
          'Nat)]
    [(? symbol?)
     (dict-ref env e)]
    [`(the ,A ,e)
     (and (type-check env e A)
          A)]
    [`(,e1 ,e2)
     (define A (type-synth env e1))
     (match A
       [`(-> ,A ,B)
        (and (type-check env e2 A)
             B)])]
    [_ (error "No synth rule for term" e)]))

;; Takes an Expr and a Type, and returns a boolean?
(define (type-check env e A)
  (match e
    [(? natural-number/c)
     (type=? A 'Nat)]
    [(? string?)
     (type=? A 'String)]
    [`(let ([,x ,e]) ,e2)
     (define B (type-synth env e))
     (type-check (dict-set env 'x B) e2 A)]
    [_
     (type=? A (type-synth env e))]))

(define type=? equal?)
