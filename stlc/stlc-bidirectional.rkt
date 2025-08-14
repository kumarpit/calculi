#lang racket
(require rackunit)

;; A simply typed lambda calculus with booleans, integers, conditionals, and
;; syntactic sugar for recursion via `letrec`. Type checking implemented 
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
    | (letrec ([x : e] ...) e)
    | e : T

x ::= symbol?

primop ::= +
         | *
         | -
         | zero?
|#

;; Value is one of:
;; - Integer
;; - Boolean

;; TODO:w
