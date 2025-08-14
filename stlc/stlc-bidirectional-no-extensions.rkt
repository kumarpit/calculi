#lang racket
(require rackunit)

;; A simply typed lambda calculus with booleans, integers, and conditionals
;; via bidirectional typing.

#|
T ::= Bool
    | Int
    | (-> T T)

STLC ::= x
    | integer?
    | boolean?
    | (λ (x) e)
    | (e e)
    | (if e e e)
    | (primop e ...)
    | e : T ;; This is the only addition to the untyped STLC syntax

x ::= symbol?

primop ::= +
         | *
         | -
         | zero?
|#

;; Value is one of:
;; - Integer
;; - Boolean

;; STLC -> Value
;; inter: Given a *well-typed* (i.e null ⊢ e: T) STLC expression, evaluates
;; its value.
(define (interp e)
  (let interp ([e e]
               [env (make-hash)])
    (match e
      [(? symbol?) (dict-ref env e)]
      [(? integer?) e]
      [(? boolean?) e]

      [`(λ (,x) ,e)
       (λ (v)
         (define env^ (dict-copy env))
         (dict-set! env^ x v)
         (interp e env^))]

      [`(if ,e1 ,e2 ,e3)
       (if (interp e1 env)
           (interp e2 env)
           (interp e3 env))]

      [`(,prim-op ,es ...)
       #:when (memq prim-op '(- + * zero?))
       (apply (eval prim-op (module->namespace 'racket/base))
              (map (curryr interp env) es))]

      [`(,e1 ,e2)
       ((interp e1 env) (interp e2 env))]

      [`(,e : ,_) (interp e env)]

      [_ (error 'interp "Invalid term: ~a" e)])))

;; Type is one of:
(struct IntType () #:transparent)
(struct BoolType () #:transparent)
(struct FunType (
                 arg ;; Type
                 body ;; Type
                 ) #:transparent)

;; S-exp -> Type
;; interp: Given any s-exp, tries to parse it as a type in the STLC language
(define (parse-type ty)
  (match ty
    ['int (IntType)]
    ['bool (BoolType)]
    [`(-> ,a ,b) (FunType (parse-type a) (parse-type b))]
    [_ (error 'parse-type "Invalid type definition: ~a is not a type" ty)]))

(define-syntax-rule (assert-type ty expected)
  (let ([ty-val ty]) ;; To avoid double evaluation
    (unless (equal? ty-val expected)
      (error 'typecheck
             "Mismatched types: Expected ~a got ~a"
             expected ty-val))))

;; S-exp -> Type
;; interp: Given any s-expression, infers the `Type` if it is a valid, well-typed
;; STLC program and if its type can be inferred, else errors.
(define (infer e env)
  (let infer ([e e]
               [env env])
    (match e
      [(? symbol?) (dict-ref env e)]
      [(? integer?) (IntType)]
      [(? boolean?) (BoolType)]

      ;; Cannot infer unannotated abstraction
      ;; [`(λ (,x) ,e) 'todo]

      ;; Cannot infer conditionals
      ;; [`(if ,e1 ,e2 ,e3) 'todo]

      [`(,prim-op ,es ...)
       #:when (memq prim-op '(- + *))
       (for ([e es])
         (assert-type (infer e env) (IntType)))
       (IntType)]

      [`(,prim-op ,es ...)
       #:when (memq prim-op '(zero?))
       (for ([e es])
         (assert-type (infer e env) (IntType)))
       (BoolType)]

      [`(,e1 ,e2)
       (let ([operator-ty (infer e1 env)])
         (begin
           (unless (FunType? operator-ty)
             (error 'infer
                    "Expected a function in operator position, got: ~a for ~a"
                    operator-ty
                    e1))
           (check e2 env (FunType-arg operator-ty))
           (FunType-body operator-ty)))]

      [`(,e : ,ty) (check e env (parse-type ty))]

      [_ (error 'infer "Cannot infer type for term, please provide an annotation: ~a" e)])))

;; S-exp -> Type
;; interp: Given any s-expression, checks if it is a valid, well-typed 
;; STLC program of the expected type, else errors 
(define (check e env expected-ty)
  (let check ([e e]
               [env env]
               [expected-ty expected-ty])
    (match e
      [`(λ (,x) ,e)
        (begin
         (unless (FunType? expected-ty)
           (error 'check 
                  "Expected a function type, got: ~a"
                  expected-ty))
         (define env^ (dict-copy env))
         (dict-set! env^ x (FunType-arg expected-ty))
         (check e env^ (FunType-body expected-ty))
         expected-ty)]

      [`(if ,e1 ,e2 ,e3)
       (begin 
         (check e1 env (BoolType))
         (check e2 env expected-ty)
         (check e3 env expected-ty))]

      ;; BT-CheckInfer 
      [_ (begin
           (assert-type (infer e env) expected-ty)
           expected-ty)])))

;; S-exp -> Value
;; interp: Run the given STLC program
(define (run/stlc e)
  (begin
    (infer e (make-hash))
    (interp e)))

; --- Basic Expression Tests ---

(check-equal? (run/stlc '5) 5)
(check-equal? (run/stlc '#t) #t)

;; --- Primitive Operations Tests ---

(check-equal? (run/stlc '(+ 1 2)) 3)
(check-equal? (run/stlc '(* 5 10)) 50)
(check-equal? (run/stlc '(- 10 3)) 7)
(check-equal? (run/stlc '(zero? 0)) #t)
(check-equal? (run/stlc '(zero? 10)) #f)

;; --- Conditional Tests ---

(check-equal? (run/stlc '((if #t 1 2) : int)) 1)
(check-equal? (run/stlc '((if #f 1 2) : int)) 2)
(check-equal? (run/stlc '((if (zero? 0) (+ 1 1) (* 2 2)) : int)) 2)

;; --- Function Application Tests ---

(check-equal? (run/stlc '(((λ (x) x) : (-> int int)) 5)) 5)
(check-equal? (run/stlc '(((λ (x) (+ x 1)) : (-> int int)) 99)) 100)

;; --- Type Error Tests ---

(check-exn exn:fail?
           (λ () (run/stlc '((if 1 2 3) : int)))
           "Mismatched types: Expected (BoolType) got (IntType)")

(check-exn exn:fail?
           (λ () (run/stlc '((if #t 1 #f) : int)))
           "Mismatched types: Expected (IntType) got (BoolType)")

(check-exn exn:fail?
           (λ () (run/stlc '(+ 1 #t)))
           "Mismatched types: Expected (IntType) got (BoolType)")

(check-exn exn:fail?
           (λ () (run/stlc '(zero? #t)))
           "Mismatched types: Expected (IntType) got (BoolType)")

(check-exn exn:fail?
           (λ () (run/stlc '(1 2)))
           "Expected a function in operator position, got: (IntType)")

(check-exn exn:fail?
           (λ () (run/stlc '(((λ (x) x) : (-> int int)) #t)))
           "Mismatched types: Expected (IntType) got (BoolType)")

(check-exn exn:fail?
           (λ () (run/stlc '(+ 1 z)))
           "'z' is unbound")
