#lang racket

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
;; inter: Given a *well-typed* STLC expression, evaluates its value.
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
(struct IntType ())
(struct BoolType ())
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
  (let ([ty-val ty])
    (unless (eq? ty-val (parse-type expected))
      (error 'typecheck
             "Mismatched types: Expected ~a got ~a"
             expected ty-val))))

;; S-exp -> Type
;; interp: Given any s-expression, returns `Type` if it is a valid, well-typed
;; STLC program.
(define (typecheck e)
  (let typecheck ([e e]
                  [env (make-hasheq)])
    (match e
      [(? symbol?) (dict-ref env e)]
      [(? integer?) (IntType)]
      [(? boolean?) (BoolType)]

      [`(λ (,x : ,ty) ,e)
       (begin
         (define env^ (dict-copy env))
         (define arg-ty (parse-type ty))
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

           (assert-type actual-ty decl-ty)
           (typecheck e env^))
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
       #:when (memq prim-op '(- + * zero?))
       (for ([e es])
         (assert-type (typecheck e) (IntType)))
       (IntType)]

      [`(,e1 ,e2)
       (let ([operator-ty (typecheck e1 env)]
             [operand-ty  (typecheck e2 env)])
        (begin 
          (unless (FunType? operand-ty) 
            (error 'typecheck 
                   "Expected a function in operator position, got: ~a"
                   operand-ty))
          (assert-type operand-ty (FunType-arg operator-ty))
          (FunType-body operator-ty)))]

      [_ (error 'interp "Invalid term: ~a" e)])))
