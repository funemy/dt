#lang racket

;; A Variable is a symbol
(define variable? symbol?)

;; An Expression is one of:
;; - an integer literal, representing an integer
;; - `(lambda (,x) ,e) is a function whose parameter is named x, where e is an expression
;; - `(app ,e1 ,e2), where e1 and e2 are expressions
;; - a Variable
;; - `(the ,Type ,Expression) is an expression

(struct clos (env param body) #:transparent)
;; A Value is one of:
;; - an integer
;; - (clos Env Variable Expression), representing the value of a function

;; A Normal form is one of:
;; - a Value
;; - a Neutral

;; TODO: Our implementation requires that when we embed a normal in a neutral,
;; we know it's type, so we at least need:
(struct the (type value) #:transparent)

;; The tutorial says we also need to know the type of all normal forms, but we
;; did not discover why:
(struct neu (type neutral) #:transparent)

;; A Neutral is one of:
;; - variable
;; - `(app ,neutral ,normal)

;; An Env is an ordered dictionary mapping Variables to Normal.
;; e.g. (dict-set '() 'x 1) maps 'x to 1
;; e.g. '() maps no variables to values
;; e.g. (dict-set (dict-set '() 'x 1) 'x 2) maps 'x to 2

;; Env Expression -> Value
(define (to-val env e)
  (match e
    [x #:when (variable? x)
       (dict-ref env x x)]
    [i
     #:when (integer? i)
     i]
    #;[`(+ ,e1 ,e2)
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
     (do-ap (to-val env e1) (to-val env e2))]
    [_ (error "Invalid expression")]))

;; Normal -> Normal -> Normal
(define (do-ap v1 v2)
  (match v1
    [(clos env1 param body)
     (to-val (dict-set env1 param v2) body)]
    [(the `(-> ,A ,B) neutral)
     `(app ,neutral ,(the A v2))]))

; Normal -> Expression
(define (read-back-normal type normal)
  (match type
    ['Int
     (match normal
       [(? integer?)
        (the 'Int normal)]
       [neutral
        (read-back-neutral neutral)])]
    ['(-> ,A ,B)
     (define x (gensym 'x))
     `(lambda (,x)
        ,(read-back-neutral
          (do-ap normal x)))
     ;; alternative implementation that is more systematic, but has duplicate code
     #;(match normal
       [(clos env param body)
        `(lambda (,param)
           ,(read-back-normal
             B
             (to-val
              env #;(dict-set env param x)
              body)))]
       [neutral
        (define x (gensym 'x))
        `(lambda (,x)
           ,(read-back-neutral
             (do-ap neutral x)))])])
  #;(match normal
    [(? integer?)
     normal]
    [(clos env param body)
     #;(define x (gensym param))
     `(lambda (,param)
        ,(read-back-normal
          (to-val
           env #;(dict-set env param x)
           body)))]
    [neutral
     (read-back-neutral neutral)]))

; Neutral -> Expression
(define (read-back-neutral neutral)
  (match neutral
    [`(app ,neutral ,(the type normal))
     `(app ,(read-back-neutral neutral)
           ,(read-back-normal type normal))]
    [(? variable?)
     neutral]))

(require rackunit)
(check-equal?
 (to-val '() 0)
 0)

(check-equal?
 (to-val '() `(+ 0 1))
 1)

;; This is where we got last time.
;; We have two questions to answer:
;; 1. what is the value of a variable?
;; 2. what is the value of a lambda?
(check-equal?
 (to-val (dict-set '() 'x 5) 'x)
 5)

(check-equal?
 (to-val '() `(lambda (x) x))
 (clos '() 'x 'x))

(check-equal?
 (to-val '() `(app (lambda (x) (lambda (y) x))
               1))
 (clos (dict-set '() 'x 1)
       'y
       'x))

;; Fails! not equiv, but... alpha-equiv?
(check-equal?
 (to-val '() `(app (lambda (y) (lambda (x) y))
                   1))
 (clos (dict-set '() 'x 1)
       'y
       'x))

(check-equal?
 (to-val '() `(app (app (lambda (x) (lambda (x) x))
                   1) 2))
 2)

;;
(define (alpha-equiv? e1 e2)
  (define (helper i xs x ys y)
    (match (cons x y)
      [(cons (? variable?) (? variable?))
       (let ([x? (dict-ref xs x #f)]
             [y? (dict-ref ys y #f)])
         (cond
           [(and x? y?)
            (equal? x? y?)]
           [(and (not x?) (not y?))
            (equal? x y)]
           [else false]))]
      [(cons `(app ,e1 ,e11)
             `(app ,e2 ,e22))
       (and (helper i xs e1 ys e2)
            (helper i xs e11 ys e22))]
      [(cons `(lambda (,x) ,e1)
             `(lambda (,y) ,e2))
       (helper (add1 i) (dict-set xs x i) e1 (dict-set ys y i) e2)]
      ;; More cases are necessary in this function
      [_ false]))
  (helper 0 '() e1 '() e2))


(check alpha-equiv?
       '(lambda (x) x)
       '(lambda (y) y))

(check (compose not alpha-equiv?)
       '(lambda (x) x)
       '(lambda (y) x))
