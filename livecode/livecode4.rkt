#lang racket

;; An Expression is one of:
;; - an integer literal, representing an integer
;; - `(+ ,e1 ,e2), where e1 and e2 are Expressions
;;    (list '+ e1 e2)
;; - `(lambda (,x) ,e) is a function whose parameter is named x, where e is an expression
;; - `(app ,e1 ,e2), where e1 and e2 are expressions

;; A Value is one of:
;; - an integer
;; -

;; Expression -> Value
(define (to-val e)
  (match e
    [i
     #:when (integer? i)
     i]
    [`(+ ,e1 ,e2)
     ;; e1 is Expression
     ;; e2 is Expression
     (let ([v1 (to-val e1)]
           [v2 (to-val e2)])
       ;; v1 is Value
       ;; v2 is Value
       (+ v1 v2))]
    [_ (error "Invalid expression")]))

(require rackunit)
(check-equal?
 (to-val 0)
 0)

(check-equal?
 (to-val `(+ 0 1))
 1)

(check-equal?
 (to-val `(app (lambda (x) (lambda (y) x))
               1))
 ???)
