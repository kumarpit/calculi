#lang racket
(require rackunit)

;; A simply typed lambda calculus with booleans, integers, conditionals, and
;; syntactic sugar for recursion via `letrec`.

#|
T ::= Bool
    | Int
    | (-> T T)

STLC ::= x
    | integer?
    | boolean?
    | (λ (x : T) e)
    | (e e)
    | (if e e e)
    | (primop e ...)
    | (letrec ([x : T = e] ...) e)

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
               [env (make-hasheq)])
    (match e
      [(? symbol?) (dict-ref env e)]
      [(? integer?) e]
      [(? boolean?) e]

      [`(λ (,x : ,_) ,e)
       (λ (v)
         (define env^ (dict-copy env))
         (dict-set! env^ x v)
         (interp e env^))]

      [`(letrec ([,xs : ,_ = ,es] ...) ,e)
       (begin
         (define env^ (dict-copy env))
         (for ([x xs]
               [e es])
           (dict-set! env^ x (interp e env^)))
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
    [`(,a -> ,b) (FunType (parse-type a) (parse-type b))]
    [_ (error 'parse-type "Invalid type definition: ~a is not a type" ty)]))

(define-syntax-rule (assert-type ty expected)
  (let ([ty-val ty]) ;; To avoid double evaluation
    (unless (equal? ty-val expected)
      (error 'typecheck
             "Mismatched types: Expected ~a got ~a"
             expected ty-val))))

;; S-exp -> Type
;; interp: Given any s-expression, returns `Type` if it is a valid, well-typed
;; STLC program.
(define (typecheck e)
  (let typecheck ([e e]
                  [env (make-hash)])
    (match e
      [(? symbol?)
       (with-handlers
           ([exn:fail:contract?
             (lambda (exn)
               (error 'lookup
                      "'~a' is unbound"
                      e))])
         (dict-ref env e))
       ]
      [(? integer?) (IntType)]
      [(? boolean?) (BoolType)]

      [`(λ (,x : ,ty) ,e)
       (begin
         (define arg-ty (parse-type ty))
         (define env^ (dict-copy env))
         (dict-set! env^ x arg-ty)
         (FunType arg-ty (typecheck e env^)))]

      [`(letrec ([,xs : ,Ts = ,es] ...) ,e)
       (begin
         (define env^ (dict-copy env))
         (for ([x  xs]
               [ty Ts]
               [e  es])
           (define decl-ty (parse-type ty))
           (dict-set! env^ x decl-ty)
           (define actual-ty (typecheck e env^))
           (assert-type actual-ty decl-ty))
         (typecheck e env^))]

      [`(if ,e1 ,e2 ,e3)
       (begin
         (assert-type (typecheck e1 env) (BoolType))
         ;; Each branch must return the same type
         (let* ([conseq-ty (typecheck e2 env)]
                [alt-ty (typecheck e3 env)])
           (assert-type conseq-ty alt-ty)
           conseq-ty))]

      [`(,prim-op ,es ...)
       #:when (memq prim-op '(- + *))
       (for ([e es])
         (assert-type (typecheck e env) (IntType)))
       (IntType)]

      [`(,prim-op ,es ...)
       #:when (memq prim-op '(zero?))
       (for ([e es])
         (assert-type (typecheck e env) (IntType)))
       (BoolType)]

      [`(,e1 ,e2)
       (let ([operator-ty (typecheck e1 env)]
             [operand-ty  (typecheck e2 env)])
         (begin
           (unless (FunType? operator-ty)
             (error 'typecheck
                    "Expected a function in operator position, got: ~a"
                    operator-ty))
           (assert-type operand-ty (FunType-arg operator-ty))
           (FunType-body operator-ty)))]

      [_ (error 'interp "Invalid term: ~a" e)])))

;; S-exp -> Value
;; interp: Run the given STLC program
(define (run/stlc e)
  (begin
    (typecheck e)
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

(check-equal? (run/stlc '(if #t 1 2)) 1)
(check-equal? (run/stlc '(if #f 1 2)) 2)
(check-equal? (run/stlc '(if (zero? 0) (+ 1 1) (* 2 2))) 2)

;; --- Function Application Tests ---

(check-equal? (run/stlc '((λ (x : int) x) 5)) 5)
(check-equal? (run/stlc '((λ (x : int) (+ x 1)) 99)) 100)
(check-equal? (run/stlc '(((λ (f : (int -> int))
                             (λ (x : int) (+ 1 (f x))))
                           (λ (y : int) (* y 2))) 5)) 11)

;; --- Letrec and Recursion Tests ---

(check-equal? (run/stlc '(letrec ([x : int = 10]) x)) 10)
(check-equal? (run/stlc '(letrec ([x : int = 1] [y : int = 2]) (+ x y))) 3)
(check-equal? (run/stlc '(letrec ([fact : (int -> int) =
                                        (λ (n : int)
                                          (if (zero? n)
                                              1
                                              (* n (fact (- n 1)))))])
                           (fact 5)))
              120)

;; --- Type Error Tests ---

(check-exn exn:fail?
           (λ () (run/stlc '(if 1 2 3)))
           "Mismatched types: Expected (BoolType) got (IntType)")

(check-exn exn:fail?
           (λ () (run/stlc '(if #t 1 #f)))
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
           (λ () (run/stlc '((λ (x : int) x) #t)))
           "Mismatched types: Expected (IntType) got (BoolType)")

(check-exn exn:fail?
           (λ () (run/stlc '(letrec ([x : int = #t]) x)))
           "Mismatched types: Expected (IntType) got (BoolType)")

(check-exn exn:fail?
           (λ () (run/stlc '(letrec ([x : 
                                             (int -> int) = 
                                             (λ (y : int) #t)]) (x 1))))
           "Mismatched types: Expected (IntType) got (BoolType)")

(check-exn exn:fail?
           (λ () (run/stlc '(+ 1 z)))
           "'z' is unbound")
