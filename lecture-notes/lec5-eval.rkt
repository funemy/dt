#lang racket

(define variable? symbol?)

;; An Expression is one of:
;; - an integer literal, representing an integer
;; - `(+ ,e1 ,e2), where e1 and e2 are Expressions
;;    (list '+ e1 e2)
;; - `(lambda (,x) ,e) is a function whose parameter is named x, where e is an expression
;; - `(app ,e1 ,e2), where e1 and e2 are expressions
;; - a variables

  (struct clos (env param body) #:transparent)
;; A Value is one of:
;; - an integer
;; - a closure, representing the value of a function

;; an env is a dictionary mapping variables to values
;; e.g. (dict-set '() 'x 1)

;; Expression -> Value
(define (to-val env e)
  (match e
    [x
     #:when (variable? x)
     (dict-ref env x)]
    [i
     #:when (integer? i)
     i]
    [`(+ ,e1 ,e2)
     ;; e1 is Expression
     ;; e2 is Expression
     (let ([v1 (to-val env e1)]
           [v2 (to-val env e2)])
       ;; v1 is Value
       ;; v2 is Value
       (+ v1 v2))]
    [`(lambda (,x) ,e)
      (clos env x e)]
    [`(app ,e1 ,e2)
      (let ([val-of-e1 (to-val env e1)]
            [val-of-e2 (to-val env e2)])
        (match val-of-e1
          [(clos env1 param body)
           (to-val (dict-set env1 param val-of-e2) body)]
          ))]
    [_ (error "Invalid expression")]))

(require rackunit)

(check-equal?
 (to-val '() 0)
 0)

(check-equal?
 (to-val '() `(+ 0 1))
 1)

;; We have two questions to answer:
;; 1. what is the value of a variable
;; 2. what is the value of a lambda

(check-equal?
  (to-val (dict-set '() 'x 5) 'x)
  5)

(check-equal? (to-val '() `(app (lambda (x) (lambda (y) x)) 1))
   (clos (dict-set '() 'x 1) 'y 'x))

