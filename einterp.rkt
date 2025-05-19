#lang racket
(require "ast.rkt" "parse.rkt")

(module+ test (require rackunit))

(struct closure (f xs e r) #:prefab)

(struct cons-ptr (a) #:prefab)
(struct box-ptr (a) #:prefab)

;; type Answer = (list (Or Value 'err) Store)

;; type Store = (Hashof Address Storeable)

;; type Storeable = (Vectorof Value)
;; tyep Address = Symbol

;; type Value =
;; | Integer
;; | Character
;; | Boolean
;; | Closure
;; | ConsPtr
;; | BoxPtr

;; type Env = (Listof (List Id Value))

;; Prog -> Answer
(define (interp p)
  (match p
    [(Prog ds e)
     (interp-env e (defns->env ds) (hash))]))

;; Defns -> Env
;; Creates a (cyclic) environment binding
;; all of the definitions to closures
(define (defns->env ds)
  (let* ([ph (make-placeholder #f)]
         [r (map list
                 (map (λ (d) (match d [(Lam f _ _) f])) ds)
                 (map (λ (d) (match d [(Lam f xs e) (closure f xs e ph)])) ds))])
    (placeholder-set! ph r)
    (make-reader-graph r)))

;; [Listof Expr] Env Store -> (list (Or (Listof Value) 'err) Store)
(define (interp-env* es r s)
  (match es
    ['() (list '() s)]
    [(cons e es)
     (match (interp-env e r s)
       ['err (list 'err s)]
       [(list v s)
        (match (interp-env* es r s)
          [(list 'err s) (list 'err s)]
          [(list vs s)
           (list (cons v vs) s)])])]))

;; Expr Env Store -> Answer
(define (interp-env e r s) 
  (match e
    [(Lit d) (list d s)]
    [(Var x) (list (interp-var e r) s)]
    [(Lam f xs e1)
     (list (closure f xs e1 r) s)]
    [(App e1 es)
     (match (interp-env e1 r s)
       [(list 'err s) (list 'err s)]
       [(list v s)
        (match (interp-env* es r s)
          [(list 'err s) (list 'err s)]
          [(list vs s)
           (apply-closure v vs s)])])]
        
    [(Prim0 p)
     (interp-prim0 p s)]
        
    [(Prim1 p e1)
     (match (interp-env e1 r s)
       [(list 'err s) (list 'err s)]
       [(list v s)
        (interp-prim1 p v s)])]
        
    [(Prim2 p e1 e2)
     (match (interp-env e1 r s)
       [(list 'err s) (list 'err s)]
       [(list v1 s)
        (match (interp-env e2 r s)
          [(list 'err s) (list 'err s)]
          [(list v2 s)
           (interp-prim2 p v1 v2 s)])])]

    [(Begin e1 e2)
     (match (interp-env e1 r s)
       [(list 'err s) (list 'err s)]
       [(list _ s) (interp-env e2 r s)])]
    
    [(If e1 e2 e3)
     (match (interp-env e1 r s)
       [(list 'err s) (list 'err s)]
       [(list v1 s)
        (if (false? v1)
            (interp-env e3 r s)
            (interp-env e2 r s))])]))                                           
  

;; Closure [Listof Value] Store -> Answer
(define (apply-closure f vs s)
  (match f
    [(closure _ xs e1 r)
     ; check arity matches
     (if (= (length xs) (length vs))
         (interp-env e1 (append (zip xs vs) r) s)
         'err)]))

;; Op0 Store -> Answer
(define (interp-prim0 op s)
  (match op
    ['read-byte (list (read-byte) s)]
    ['peek-byte (list (peek-byte) s)]
    ['void      (list (void) s)]))

;; Op1 Value Store -> Answer
(define (interp-prim1 op v s)
  (match (list op v)
    [(list 'add1 (? integer?))            (list (add1 v) s)]
    [(list 'sub1 (? integer?))            (list (sub1 v) s)]
    [(list 'zero? (? integer?))           (list (zero? v) s)]
    [(list 'char? v)                      (list (char? v) s)]
    [(list 'integer->char (? codepoint?)) (list (integer->char v) s)]
    [(list 'char->integer (? char?))      (list (char->integer v) s)]
    [(list 'write-byte    (? byte?))      (list (void) s)]
    [(list 'eof-object? v)                (list (eof-object? v) s)]
    [(list 'car (cons-ptr a))
     (list (vector-ref (hash-ref s a) 0) s)]
    [(list 'cdr (cons-ptr a))
     (list (vector-ref (hash-ref s a) 1) s)]
    [(list 'box v)
     (let ((a (gensym)))
       (list (box-ptr a)
             (hash-set s a (vector v))))]
    [(list 'unbox (box-ptr a))
     (list (vector-ref (hash-ref s a) 0) s)]
     
    [_ (list 'err s)]))

;; Op2 Value Value Store -> Answer
(define (interp-prim2 op v1 v2 s)
  (match (list op v1 v2)
    [(list '+ (? integer?) (? integer?)) (list (+ v1 v2) s)]
    [(list '- (? integer?) (? integer?)) (list (- v1 v2) s)]
    [(list '< (? integer?) (? integer?)) (list (< v1 v2) s)]
    [(list '= (? integer?) (? integer?)) (list (= v1 v2) s)]
    [(list 'cons v1 v2)
     (let ((a (gensym)))
       (list (cons-ptr a)
             (hash-set s a (vector v1 v2))))]    
    [_ (list 'err s)]))
         
;; Any -> Boolean
(define (codepoint? v)
  (and (integer? v)
       (or (<= 0 v 55295)
           (<= 57344 v 1114111))))

;; Var Env -> Value
(define (interp-var e r)
  (match e
    [(Var x)
     (lookup r x)]))

(define (zip xs ys)
  (match* (xs ys)
    [('() '()) '()]
    [((cons x xs) (cons y ys))
     (cons (list x y)
           (zip xs ys))]))

;; Env Variable -> Answer
(define (lookup env x)
  (match env
    ['() 'err]
    [(cons (list y i) env)
     (match (symbol=? x y)
       [#t i]
       [#f (lookup env x)])]))

;; Env Variable Value -> Value
(define (ext r x i)
  (cons (list x i) r))
