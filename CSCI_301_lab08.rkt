#lang racket
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; CSCI 301, Winter 2018
;;
;; Lab #5
;;
;; Nick Amundsen
;; W01323151
;;
;; The purpose of this program is to
;; evaluate expressions recursively
;; using a set environment, adding the lambda functions.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide lookup)
(provide evaluate)

;Environment that was given to us
(define env (list
(list 'x 5)
(list '+ +)
(list '* *)
(list '= equal?)
(list 'else #t)))

(define NewEnv (list
(list 'x 5)
(list '+ +)
(list '* *)
(list '= equal?)
(list 'else #t)))

;Test environment
(define e1  (map list
                 '(     x  y  z + - * cons car cdr nil list = else )
                 (list 10 20 30 + - * cons car cdr '() list = #t   )))


;Let function
(define eval-let
  (lambda (ls env)
    (if (null? (cdr ls)) (cons (cons (car(car ls)) (list (evaluate (car(cdr(car ls))) env))) '())
        (cons (cons (car(car ls)) (list (evaluate (car(cdr(car ls))) env))) (eval-let (cdr ls) env)))
    ))



;Cond function
(define eval-cond
  (lambda (list env)
    (if (eqv? (evaluate (car(car list)) env) #t) (eval-list (car(cdr(car list))) env) (eval-cond (cdr list) env))
    ))


;Function to check if a list is a special form
(define special-form?
  (lambda (list)
    (cond ((not (list? list)) #f)
          ((eqv? (car list) 'if) #t)
          ((eqv? (car list) 'cond) #t)
          ((eqv? (car list) 'let) #t)
          ((eqv? (car list) 'lambda) #t)
          ((eqv? (car list) 'letrec) #t)
          (else #f))))


;Function to evaluate special form expressions
(define evaluate-special-form
  (lambda (list env)
    (cond ((and (eqv? (car list) 'if) (eqv? (evaluate (car(cdr list)) env) #t)) (evaluate (car(cdr(cdr list))) env))
          ((and (eqv? (car list) 'if) (eqv? (evaluate (car(cdr list)) env) #f)) (evaluate (car(cdr(cdr(cdr list)))) env))
          ((eqv? (car list) 'cond) (eval-cond (cdr list) env))
          ((eqv? (car list) 'let) (evaluate (car(cdr(cdr list))) (append (eval-let (car(cdr list)) env) env)))
          ((eqv? (car list) 'lambda) (eval-lambda list env))
          ((eqv? (car list) 'letrec) (eval-letrec list env))
          (else (error "cannot evaluate special-form"))
          )))


;Function to evaluate a letrec
(define eval-letrec
  (lambda (list env)
    (let ([NewEnv (append (make-new-env (car(cdr list)) (make-fake-env (car(cdr list)) env)) env)])
      (evaluate (car(cdr(cdr list))) (change-env NewEnv NewEnv))
      )))

;Function to change the environment for each closure
(define change-env
  (lambda (NewEnv closure-list)
    (cond ((null? closure-list) NewEnv)
          ((closure-search NewEnv (car closure-list)) (set-closure-env! (cdr(car closure-list)) NewEnv)  (change-env (append (cons (car closure-list) '()) NewEnv) (cdr closure-list)))
          (else (change-env NewEnv (cdr closure-list)))
          )))

;Function to look for closure in env
(define closure-search
  (lambda (env cl)
    (cond ((null? env) #f)
          ((and (eqv? (car(car env)) (car cl)) (closure? (cdr(car env)))) #t)
          (else (closure-search (cdr env) cl))
          )))


;Function to create fake closures with fake env for letrec
(define make-fake-env
  (lambda (list env)
    (cond ((null? (cdr list)) (cons (eval-lambda (car(cdr(car list))) env) '()))
          (else (cons (eval-lambda (car(cdr(car list))) env) (make-fake-env (cdr list) env)))
          )))

;Function to recursively create the NewEnv with closures and symbols
(define make-new-env
  (lambda (list closure-list)
    (cond ((null? (cdr closure-list)) (cons (cons (car(car list)) (car closure-list)) '()))
          (else (cons (cons (car(car list)) (car closure-list)) (make-new-env (cdr list) (cdr closure-list)))))))

;Function to evaluate lambda special form
(define eval-lambda
  (lambda (list env)
    (closure (car(cdr list)) (car(cdr(cdr list))) env)))



;Function to look up symbol inside an environment
(define lookup
  (lambda (s env)
    (cond ((empty? env) (error (string-append (~a s) ": not in environment")))
          ((not (symbol? s)) (error (string-append (~a s) ": not a symbol")))
          ((eqv? s 'cond) s)
          ((eqv? s 'if) s)
          ((and (eqv? (car (car env)) s) (closure? (cdr(car env)))) (cdr(car env)))
          ((eqv? (car (car env)) s) (car (cdr (car env))))
          (else (lookup s (cdr env)))         
          )))


;Function to evaluate each expression inside a list
(define eval-list
  (lambda (exp env)
    (cond ((empty? exp) '())
          ((and (not (list? exp)) (number? exp)) exp)
          ((and (not (list? exp)) (symbol? exp)) (lookup exp env))
          ((number? (car exp)) (cons (car exp) (eval-list (cdr exp) env)))
          ((and (symbol? (car exp)) (not(special-form? exp))) (cons (lookup (car exp) env) (eval-list (cdr exp) env)))
          ((special-form? exp) (evaluate-special-form exp env))
          ((list? (car exp)) (cons (evaluate (car exp) env) (eval-list (cdr exp) env)))
          )))

;Function to apply a procedure  
(define evaluate
  (lambda (exp env)
    (let ((exp-eval (eval-list exp env)))
      (cond ((not (list? exp-eval)) exp-eval)
            (else (apply-function exp-eval))
          ))))

;Function to go through a closure list
(define apply-closure
  (lambda (list)
    (evaluate (closure-expr (car list)) (append-env  (closure-vars (car list)) (closure-env (car list)) (cdr list)))
    ))

;Function to append the environment for a closure
(define append-env
  (lambda (var env val)
    (cond ((null? val) env)
          (else (append-env (cdr var) (append (list (cons (car var) (list (car val)))) env) (cdr val))))
    ))


;Function to apply our procedurse or closures
(define apply-function
  (lambda (list)
    (cond ((procedure? (car list)) (apply (car list) (cdr list)))
          ((number? (car list)) list)
          ((closure? (car list)) (apply-closure list))
          ((closure? (car(car list))) (apply-closure list))
          (else (error "unknown function type")))))



;Struct code?
(struct closure (vars expr (env #:mutable)))
(define print-closure
  (lambda (cl)
    (display (list 'closure (closure-vars cl) (closure-expr cl) (closure-env cl)))))



;;;;;; Tests.
;(evaluate-special-form '(if (= 1 1) 3 4) env)
;(evaluate '(if (= 1 2) 3 4) env)
;(evaluate '(+ 3 x (+ 2 2) (* 2 (+ 4 1))) env)
;(lookup 'x env)
;(evaluate '10 env)
;(evaluate '(cond ((= 1 2) (+ 1 1))
;                        ((= 2 3) (+ 2 2))
 ;                       ((= 3 3) (+ 3 3))
  ;                      (else (+ 4 4))) env)
;(evaluate '(if (= 1 2) 2 3) env)
;(eval-let
;'((x (+ 2 2))
;(y x)
;(z (* 3 3))) env)
;(cons 3 (list 3))
;(evaluate '(let ((a 1) (b 2)) (+ a b)) e1)
;(print-closure (eval-list '(lambda (x) (* x x)) 2))
;(evaluate '(let ((f (lambda (a) (lambda (b) (+ a b)))))
;                    (let ((g (f 10))
 ;                         (h (f 20)))
  ;                    (list (g 100) (h 100)))) e1)

;(print-closure (closure '(a b) '(+ a b) '((x 1) (y 2))))
;(closure '(a b) '(+ a b) '((x 1) (y 2)))


;(evaluate '(letrec ((plus (lambda (a b) (if (= a 0) b (+ 1 (plus (- a 1) b)))))
 ;        (even? (lambda (n) (if (= n 0) (= 1 1) (odd? (- n 1)))))
  ;       (odd? (lambda (n) (if (= n 0) (= 1 2) (even? (- n 1))))))
   ;          (even? (plus 4 5))) e1)

;(eval-letrec '(letrec ((plus (lambda (a b) (if (= a 0) b (+ 1 (plus (- a 1) b)))))
    ;     (even? (lambda (n) (if (= n 0) (= 1 1) (odd? (- n 1)))))
     ;    (odd? (lambda (n) (if (= n 0) (= 1 2) (even? (- n 1))))))
      ;       (even? (plus 4 5))) e1)


;(define cl1 (closure '(a b) '(+ a b) '((x 1) (y 2))))
;(define cl2 (closure '(a c) '(+ a c) '((x 1) (y 2))))
;(define l1 (cons cl1 cl2))
;(set-closure-env! (car l1) NewEnv)
;(print-closure (car l1))
