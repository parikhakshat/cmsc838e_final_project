#lang racket
(require "ast.rkt")
;(require "interp-prim.rkt")
(require "env.rkt")

(module+ test (require rackunit))

(struct closure (xs e r) #:transparent)

;(define (f x) (add1 x))
;(list (f 1) (f 2))

;; type Answer = Value | 'err

;; type Env = (Listof (List Id Value))

;; type Table = (Hashof Expr (Setof Answer))

;; Prog -> (list Answer Table)
(define (interp p)
  (match p
    [(Prog ds e)
     (interp-env e '() ds)]))

;; Expr Env Defns -> (list Answer Table)
(define (interp-env e r ds)
  (match e
    [(Lit d) (list d (hasheq e (set d)))]
    [(Var x) (interp-var e r ds)]
    [(Lam f xs e1)
     (let ((fun (closure xs e1 r)))
       (list fun (hasheq e (set fun))))]
    [(App e1 es)
     (match (interp-env e1 r ds)
       [(list 'err t1) (list 'err (table-extend t1 e 'err))]
       [(list f t1)
        (match (interp-env* es r ds)
          [(list 'err t) (list 'err (table-extend t e 'err))]
          [(list vs t)
           (if (closure? f)
               (match (apply-closure f vs ds)
                 [(list a t2)
                  (list a (table-extend (table-join (table-join t1 t) t2) e a))])                                
               (list 'err (table-extend (table-join t1 t) e 'err)))])])]
    [(Prim0 p)
     (let ((a (interp-prim0 p)))
       (list a (hasheq e (set a))))]     
    [(Prim1 p e1)
     (match (interp-env e1 r ds)
       [(list 'err t1) (list 'err (table-extend t1 e 'err))]
       [(list v t1)
        (let ((a (interp-prim1 p v)))
          (list a (table-extend t1 e a)))])]
    [(Begin e1 e2)
     (match (interp-env e1 r ds)
       [(list 'err t1) (list 'err (table-extend t1 e 'err))]
       [(list _ t1)
        (match (interp-env e2 r ds)
          [(list a t2) (list a (table-extend (table-join t1 t2) e a))])])]
    [(If e1 e2 e3)
     (match (interp-env e1 r ds)
       [(list 'err t1) (list 'err (table-extend t1 e 'err))]
       [(list v t1)
        (if v
            (match (interp-env e2 r ds)
              [(list a t2)
               (list a (table-extend (table-join t1 t2) e a))])
            (match (interp-env e3 r ds)
              [(list a t3)
               (list a (table-extend (table-join t1 t3) e a))]))])]))

;; Closure [Listof Value] Defns -> (list Answer Table)
(define (apply-closure f vs ds)
  (match f
    [(closure xs e1 r)
     ; check arity matches
     (if (= (length xs) (length vs))
         (interp-env e1 (append (zip xs vs) r) ds)
         (list 'err (hasheq)))]))
     
(define (interp-env* es r ds)
  (match es
    ['() (list '() (hasheq))]
    [(cons e es)
     (match (interp-env e r ds)
       [(list 'err t) (list 'err t)]
       [(list v t1)
        (match (interp-env* es r ds)
          [(list 'err t) (list 'err (table-join t1 t))]
          [(list vs t)
           (list (cons v vs)
                 (table-join t1 t))])])]))



;; Op0 -> Answer
(define (interp-prim0 op)
  (match op
    ['read-byte (read-byte)]
    ['peek-byte (peek-byte)]
    ['void      (void)]))

;; Op1 Value -> Answer
(define (interp-prim1 op v)
  (match (list op v)
    [(list 'add1 (? integer?))            (add1 v)]
    [(list 'sub1 (? integer?))            (sub1 v)]
    [(list 'zero? (? integer?))           (zero? v)]
    [(list 'char? v)                      (char? v)]
    [(list 'integer->char (? codepoint?)) (integer->char v)]
    [(list 'char->integer (? char?))      (char->integer v)]
    [(list 'write-byte    (? byte?))      (write-byte v)]
    [(list 'eof-object? v)                (eof-object? v)]
    [(list 'box v)                        (box v)]
    [(list 'unbox (? box?))               (unbox v)]
    [(list 'car (? pair?))                (car v)]
    [(list 'cdr (? pair?))                (cdr v)]
    [(list 'empty? v)                     (empty? v)]
    [(list 'cons? v)                      (cons? v)]
    [(list 'box? v)                       (box? v)]
    [(list 'vector? v)                    (vector? v)]
    [(list 'vector-length (? vector?))    (vector-length v)]
    [(list 'string? v)                    (string? v)]
    [(list 'string-length (? string?))    (string-length v)]
    [_ 'err]))

#|
;; Op0 -> [Setof Answer]
(define (interp-prim0 op)
  (match op
    ['read-byte (set (Int) eof) #;(set (read-byte))]
    ['peek-byte (set (Int) eof) #;(set (peek-byte))]
    ['void      (set (void))]))

;; Op1 Value -> [Setof Answer]
(define (interp-prim1 op v)
  (match (list op v)
    [(list 'add1 (? integer?))            (set (add1 v))]
    [(list 'add1 (Int))                   (set (Int))]
    [(list 'sub1 (? integer?))            (set (sub1 v))]
    [(list 'sub1 (Int))                   (set (Int))]
    [(list 'zero? (? integer?))           (set (zero? v))]
    [(list 'zero? (Int))                  (set #t #f)]    
    [(list 'char? v)                      (set (char? v))]
    [(list 'integer->char (? codepoint?)) (set (integer->char v))]
    [(list 'integer->char (Int))          (set (Char) 'err)]
    [(list 'char->integer (? char?))      (set (char->integer v))]
    [(list 'write-byte    (Int))          (set (void) 'err)]
    [(list 'write-byte    (? byte?))      (set (void)) #;(set (write-byte v))]    
    [(list 'eof-object? (Abs))            (set #f)]
    [(list 'eof-object? v)                (eof-object? v)]
    [_ (set 'err)]))
|#

;; Any -> Boolean
(define (codepoint? v)
  (and (integer? v)
       (or (<= 0 v 55295)
           (<= 57344 v 1114111))))






;; Table Expr Answer -> Table
(define (table-extend t e a)
  (hash-update t e (λ (as) (set-add as a)) (set a)))

(module+ test
  (let ((e (Var 'x)))
    (check-equal? (table-extend (hasheq) e 1)
                  (hasheq e (set 1)))
    (check-equal? (table-extend (hasheq e (set 1)) e 2)
                  (hasheq e (set 1 2)))))
    
  
;; Table Table -> Table
(define (table-join t1 t2)
  (for/hasheq ([k (list->seteq (append (hash-keys t1) (hash-keys t2)))])
    (values k (set-union (hash-ref t1 k (set))
                         (hash-ref t2 k (set))))))

(module+ test
  (check-equal? (table-join (hasheq) (hasheq)) (hasheq))
  (let ((e (Var 'x)))
    (check-equal? (table-join (hasheq e (set 1)) (hasheq))
                  (hasheq e (set 1)))
    (check-equal? (table-join (hasheq e (set 1)) (hasheq e (set 1)))
                  (hasheq e (set 1)))
    (check-equal? (table-join (hasheq e (set 1)) (hasheq e (set 2)))
                  (hasheq e (set 1 2)))))

;; Var Env [Listof Defn] -> (list Answer Table)
(define (interp-var e r ds)
  (match e
    [(Var x)
     (match (lookup r x)
       ['err (match (defns-lookup ds x)
               [(Defn f xs e) (interp-env (Lam f xs e) '() ds)]
               [#f (list 'err (hasheq e (set 'err)))])]
       [v (list v (hasheq e (set v)))])]))

;; Defns Symbol -> Defn
(define (defns-lookup ds f)
  (findf (match-lambda [(Defn g _ _) (eq? f g)])
         ds))

(define (zip xs ys)
  (match* (xs ys)
    [('() '()) '()]
    [((cons x xs) (cons y ys))
     (cons (list x y)
           (zip xs ys))]))


    