#lang racket
(require rackunit)

;; A gradually typed lambda calculus with booleans, integers, and conditionals,
;; lazy cast checking, and blame assigned to down (? -> ...) casts.

#|
T ::= Bool
    | Int
    | (-> T T)
    | ? <-- dyn type

GTLC ::= x
    | integer?
    | boolean?
    | (λ (x : T) e)
    | (λ (x) e) <-- argument defaults to dyn type
    | (e e l)
    | (if e e e l)
    | (primop e ...)
    | (cast e : T => T)
    | (e : T l) <-- cast

x ::= symbol?
l ::= blame labels

primop ::= inc
         | dec
         | zero?
|#

;; BlameLabel is just a positive integer

;; Value is one of:
;; - Integer
;; - Boolean
;; - Function
;; - (cast <BlameLabel> <Value> : I => ?)
;; - (cast <BlameLabel> <Value> : (-> T1 T2) => (-> T3 T4))

;; Type Type -> Boolean
;; interp. Returns true if the given two types are consistent, false otherwise 
(define (consistent? T1 T2)
  (match `(,T1 ,T2)
    [`(,T1 ?) #t]
    [`(? ,T2) #t]
    [`(int int) #t]
    [`(bool bool) #t]
    [`((-> ,T11 ,T12) (-> ,T21 ,T22))
     (and (consistent? T11 T21) (consistent? T12 T22))]
    [_ #f]))

;; Type Type -> Type
;; interp. Constructs the least dynamic type that is consistent with both T1, T2
;; EFFECT: errors if types are inconsistent
(define (meet T1 T2)
  (match `(,T1 ,T2)
    [`(,T1 ?) T1]
    [`(? ,T2) T2]
    [`(int int) 'int]
    [`(bool bool) 'bool]
    [`((-> ,T11 ,T12) (-> ,T21 ,T22))
     (and (meet T11 T21) (meet T12 T22))]
    [_ (error "Inconsistent types: ~a ~a" T1 T2)]))


;; Primop | Integer | Boolean -> Type
;; interp. Determines the types of constants and primitive operators in GTLC
;; EFFECT: errors if the given expression is not a contant or operator
(define (typeof k)
  (match k
    [(? integer?) 'int]
    [(? boolean?) 'bool]
    ['inc '(-> int int)]
    ['dec '(-> int int)]
    ['zero? '(-> int bool)]
    [_ (error "~a is not a constant or operator" k)]))

;; GTLC -> Boolean
;; interp. Returns true if the given GTLC expression is a constant
(define (constant? k) (or (integer? k) (boolean? k)))

;; GTLC -> Boolean
;; interp. Returns true if the given GTLC expression is an operator
(define (operator? op) (memq op '(inc dec zero?)))


;; BlameLabel GTLC Type Type -> GTLC
;; interp. Inserts a cast around the given GTLC expression if the T1 and T2 do
;; not match
(define (make-cast l e T1 T2)
  (if (eq? T1 T2)
      e
      `(cast ,l ,e : ,T1 => ,T2)))

(define-syntax letT
  (syntax-rules ()
    [(letT [x : T label = e] b)
     `((λ (x : T) ,b) e label)]))

(define-syntax letT*
  (syntax-rules ()
    [(letT* ([x : T label = e]) b) (letT [x : T label = e] b)]
    [(letT* ([x : T label = e] [rest ...]) b)
     `((λ (x : T) ,(letT* ([rest ...]) b)) e label)]))

(define eg1
  (letT* ([f0 : ? 0 = (λ (x : int) (inc x 2))]
          [f1 : (-> bool bool) 1 = f0])
         '(f1 #t 3)))

;; Which yields:
;; '((λ (f0 : ?)
;;     ((λ (f1 : (-> bool bool))
;;        (f1 #t))
;;      f0))
;;   (λ (x : int)
;;     (inc x)))

;; Notice that cast from (-> int int) -> ? -> (-> Bool Bool)
;; This should produce an error -- but which cast should we blame?

;; (Env Symbol Type) GTLC BlameLabel -> (GTLC Type)
;; interp. Like typecheck, focussed on primitive operator applications
(define (typecheck/op-app env op e label)
  (match `(,(typecheck env e) ,(typeof op))
    [`((,new-e ,T) (-> ,T1 ,T2)) #:when (consistent? T T1)
                                 `((,op ,(make-cast label new-e T T1)) ,T2)]
    [_ (error 'typecheck
              "Invalid argument type ~a for ~a" e op)]))

;; (Env Symbol Type) GTLC GTLC GTLC BlameLabel -> (GTLC Type)
;; interp. Like typecheck, focussed on conditional expressions
(define (typecheck/if env cond conseq alt label)
  (match `(,(typecheck env cond) ,(typecheck env conseq) ,(typecheck env alt))
    [`((,new-cond ,condT) (,new-conseq ,conseqT) (,new-alt ,altT))
     #:when (and (consistent? condT 'bool) (consistent? conseqT altT))
     (let ([T (meet conseqT altT)])
       `((if ,(make-cast label new-cond condT 'bool)
             ,(make-cast label new-conseq conseqT T)
             ,(make-cast label new-alt altT T))
         ,T))]
    [`((,new-cond ,condT) (,new-conseq ,conseqT) (,new-alt ,altT))
     #:when (not (consistent? condT 'bool))
     (error 'typecheck "Expected bool for condition, got ~a" cond)]
    [_ (error 'typecheck "Inconsistent branch types in conditional: ~a and ~a"
              conseq alt)]))

;; (Env Symbol Type) Symbol Type GTLC -> (GTLC Type)
;; interp. Like typecheck, focussed on lambda definitions
(define (typecheck/lambda-def env x T  e)
  (define env^ (hash-copy env))
  (hash-set! env^ x T)
  (match (typecheck env^ e)
    [`(,new-e ,retT) `((λ (,x : ,T) ,new-e) (-> ,T ,retT))]))

;; (Env Symbol Type) GTLC Type BlameLabel -> (GTLC Type)
;; interp. Like typecheck, focussed on GTLC casted expressions
;; EFFECT: Errors if the casting is between inconsistent types
(define (typecheck/cast env e T label)
  (match (typecheck env e)
    [`(,new-e ,newT) #:when (consistent? T newT)
                     `(,(make-cast label e newT T) ,T)]
    [`(,_ ,newT) (error 'typecheck "Cannot cast from ~a to ~a" newT T)]))

;; (Env Symbol Type) GTLC GTLC BlameLabel -> (GTLC Type)
;; interp. Like typecheck, focussed on lambda applications
;; EFFECT: Errors if arg/param types are inconsistent or e1 isn't a function
(define (typecheck/lambda-app env e1 e2 label)
  (match `(,(typecheck env e1) ,(typecheck env e2))
    [`((,new-e1 ?) (,new-e2 ,e2T))
     `((,(make-cast label new-e1 '? `(-> ,e2T ?)) ,new-e2) ,e2T)]
    [`((,new-e1 (-> ,T11 ,T12)) (,new-e2 ,e2T))
     (if (consistent? T11 e2T)
         `((,new-e1 ,(make-cast label new-e2 e2T T11)) ,T12)
         (error 'typecheck "arg/param mismatch ~a / ~a" e2T T12))]
    [`((,new-e1 ,e1T) ,_)
     (error 'typecheck "Expected function, got ~a of type ~a" new-e1 e1T)]))

;; (Env Symbol Type) GTLC -> (GTLC Type)
;; interp. Given a type environment and an GTLC expression, returns the
;; expression with casts inserted where needed, as well as the expression's
;; type
(define (typecheck env e)
  (match e
    [(? constant?) `(,e ,(typeof e))]
    [`(,op ,e ,label) #:when (operator? op) (typecheck/op-app env op e label)]
    [`(if ,cond ,conseq ,alt ,label) (typecheck/if env cond conseq alt label)]
    [x #:when (symbol? x) `(,x ,(hash-ref env x))]
    [`(λ (,x) ,e) (typecheck env `(λ (,x : ?) ,e))]
    [`(λ (,x : ,T) ,e) (typecheck/lambda-def env x T e)]
    [`(,e : ,T ,label) (typecheck/cast env e T label)]
    [`(,e1 ,e2 ,label) (typecheck/lambda-app env e1 e2 label)]
    [_ (error 'typecheck "Invalid GTLC: ~a" e)]))

;; ^ Blame labels are needed wherever casts may be evaluated, i.e:
;; - function application
;; - explicit type decls
;; - conditionals (branches are casted to the same type)

; (typecheck (make-hash) `(inc 1))
; (typecheck (make-hash) `(inc #t))

; (typecheck (make-hash) `(if #t 1 2))
; (typecheck (make-hash) `(if 1 2 3))
; (typecheck (make-hash) `(if #t 1 #f))

; (typecheck (hash 'x 'int) 'x)
; (typecheck (hash 'x 'int) 'y)

(typecheck (make-hash) eg1)

;; ^ which gives:
#|
'(((λ (f0 : ?)
     ((λ (f1 : (-> bool bool))
        (f1 #t))
      (cast f0 : ? => (-> bool bool))))
   (cast (λ (x : int)
           (inc x))
         : (-> int int) => ?))
  bool)
|#

(define-syntax letB
  (syntax-rules ()
    [(_ [x e1] e2)
     (match e1
       [`(blame ,label) `(blame ,label)]
       [v (let [(x v)] e2)])]))

;; Operator Value -> Value
;; interp. Given a valid operator in GTLC, performs the operation on the given
;; value
(define (delta op v)
  (match op
    ['inc (add1 v)]
    ['dec (sub1 v)]
    ['zero? (= 0 v)]))

;; Type Type -> Boolean
;; interp. Checks if the given types are shallowly consistent
(define (shallow-consistent? T1 T2)
  (match `(,T1 ,T2)
    [`(,T ?) #t]
    [`(? ,T) #t]
    ['(int int) #t]
    ['(bool bool) #t]
    [`((-> ,T11 ,T12) (-> ,T21 ,T22)) #t] ; <-- shallow check
    [_ #f]))


;; BlameLabel GTLC Type Type -> GTLC
;; interp. Applys run-time cast on a value -- if the source and target type are
;; inconsistent (shallow), returns a blame, otherwise applys the cast
(define (apply-cast label1 v T1 T2)
  (begin (printf "checking if consistent: ~a and ~a for v: ~a = ~a\n"
                 T1
                 T2
                 v
                 (shallow-consistent? T1 T2))
         (cond [(shallow-consistent? T1 T2)
                (match T1
                  ['? (match v
                        [`(cast ,label2 ,v2 : ,T3 => ?)
                         (apply-cast label1 v2 T3 T2)])]
                  [_ (make-cast label1 v T1 T2)])]
               [#t `(blame ,label1)])))


;; GTLC Value -> Value
;; interp. Applys the function F to the value v, unwrapping any casts
(define (apply-fn/lazy F v)
  (match F
    [`(cast ,label ,F1 : (-> ,T1 ,T2) => (-> ,T3 ,T4))
     (letB [x3 (apply-cast label v T3 T1)]
           (letB [x4 (apply-fn/lazy F1 x3)]
                 (apply-cast label x4 T2 T4)))]
    [proc #:when (procedure? proc) (proc v)]))

;; (EnvOf Symbol Value) GTLC -> Value
;; interp. Interprets a well-typed GTLC programm
(define (interp env e)
  (match e
    [k #:when (constant? k) k]
    [`(,op ,e) #:when (operator? op)
               (letB [v (interp env e)] (delta op v))]
    [`(if ,cond ,conseq ,alt)
     (letB [v (interp env cond)]
           (if v (interp env conseq) (interp env alt)))]
    [x #:when (symbol? x) (hash-ref env x)]
    [`(λ (,x : ,T) ,e) (λ (v) (begin (define env^ (hash-copy env))
                                     (hash-set! env^ x v)
                                     (interp env^ e)))]
    [`(,e1 ,e2) (letB [x1 (interp env e1)]
                      (letB [x2 (interp env e2)]
                            (apply-fn/lazy x1 x2)))]
    [`(cast ,label ,e : ,T1 => ,T2)
     (letB [x (interp env e)]
           (apply-cast label x T1 T2))])) ; <-- this means (cast ...) is a value

;; S-Exp -> Value
;; Given any s-exp, evaluates it as a GTLC expression
;; EFFECT: errors if invalid GTLC
(define (eval e)
  (match (typecheck (make-hash) e)
    [`(,new-e ,T) (begin
                    (printf "cast inserted: ~a type: ~a \n" new-e T)
                    (interp (make-hash) new-e))]))


(eval eg1)

(eval (letT* ([x : ? 0 = 1]
              [y : ? 1 = 2])
             '(if #t x y 3)))

(eval (letT* ([x : int 0 = 1]
              [y : int 1 = 2])
             '(if #t x y 3)))

(eval (letT* ([x : ? 0 = 1]
              [y : bool 1 = x])
             '(if #t x y 3)))

(eval (letT* ([x : ? 0 = 1])
             '(inc x 1)))

(eval (letT* ([x : ? 0 = (λ (x : int) (inc x 1))]
              [y : (-> bool bool) 2 = x]) ; lazy, so will not catch
             '(x 1 3)))