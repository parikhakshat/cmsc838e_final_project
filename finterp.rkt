#lang racket
(provide analyze
         (struct-out Int)
         (struct-out Char)
         (struct-out closure)
         err?
         type-integer?
         type-proc?
         known-lambda?)
(require "ast.rkt"
         "parse.rkt")

(module+ test (require rackunit))

(struct closure (f xs e r) #:prefab)

(struct Abs () #:transparent)
(struct Int Abs () #:transparent)
(struct Char Abs () #:transparent)

(struct abs-vector (v) #:transparent)

;; type Answer = (list (Or Value 'err) Store)

;; type Store = (Hashof Address (Setof Storeable))

;; type Storeable = (Vectorof Value)
;;                | (abs-vector Value)

;; tyep Address = Natural (concrete) | Expr (abstract)
;; type Value =  ...
;;            | (cons-ptr Address)
;;            | (box-ptr Address)
;;            | (vec-ptr Address)
;;            | (Int) | (Char)
;; type Env = (Listof (List Id Value))

(struct cons-ptr (a) #:prefab)
(struct box-ptr (a) #:prefab)
(struct vec-ptr (a) #:prefab)

;; type Table = (Hashof Expr (Setof Answer))

;; Prog -> (list (Setof Answer) Table)
(define (interp p)
  (interp/t p (hasheq)))

;; Prog Table -> (list (Setof Answer) Table)
;; Uses t as "fall back" whenever a loop is encountered
(define (interp/t p t)
  (match p
    [(Prog ds e)
     (interp-env e (defns->env ds) (hasheq) (list (set) t))]))

;; Prog -> (list (Setof Answer) Table)
;; Computes a fixed point of interp/t
(define (interp-fixed p)
  (define (loop t0)
    (match (interp/t p t0)
      [(list as t1)
       (if (equal? t0 t1)
           (list as t1)
           (loop t1))]))
  (loop (hasheq)))

;; Prog -> Table
(define (analyze p)
  (parameterize ([current-abstract? #t])
    (match (interp-fixed p)
      [(list _ t) t]))) 

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

;; type Result = (list (Setof Answer) Table)

(define (results-extend e t0 rs)
  (let ((xs (if (set-empty? rs) rs (apply set-union (set-map rs first)))))
    (list xs
          (table-extend 
           (foldr table-join t0 (set-map rs second) #;(hasheq))
           e xs))))

(define (result-extend e t0 r)
  (match r
    [(list as t)
     (list as (table-extend (table-join t0 t) e as))]))

(define (return e a)
  (returns e (set a)))

(define (returns e as)
  (list as (hasheq e as)))


;; [Listof Expr] Env Store Seen ->
;;   -> (list (Setof (U (list (Listof Value) s) (list 'err s))) Table)

(define (interp-env* es r s seen)
  (match es
    ['() (list (set (list '() s)) (hasheq))]
    [(cons e es)
     (match (interp-env e r s seen)
       [(list as t1)
        (result-join-table
         (results-join
          (for/set ([a (in-set as)])
            (match a
              [(list 'err s) (list (set (list 'err s)) (hasheq))]
              [(list v s)
               (match (interp-env* es r s seen)
                 [(list rs t2)
                  (list (for/set ([r (in-set rs)])
                          (match r
                            [(list 'err s) (list 'err s)]
                            [(list vs s)   (list (cons v vs) s)]))
                        t2)])])))
         t1)])]))

#|
;; type Seen = (Setof (list Expr Env))
(define empty-seen set)
(define seen-member? set-member?)
(define seen-add set-add)
|#

;; type Seen = (list (Setof (list Expr Env Store)) Table)
(define (empty-seen) (list (set) (hasheq)))
(define (seen-member? s x)
  (match s
    [(list s _) (set-member? s x)]))
(define (seen-add s x)
  (match s
    [(list s t) (list (set-add s x) t)]))
(define (seen-lookup s e)
  (match s
    [(list _ t) (table-lookup t e)]))


;; Expr Env Store Seen -> (list (Setof Answer) Table)
(define (interp-env e r s seen)
  (cond
    [(seen-member? seen (list e r s))
     (define as (seen-lookup seen e))
     (list as (hasheq e as))]
    [else
     (define seen* (seen-add seen (list e r s)))
     (match e
       [(Lit d) (return e (list d s))]
       [(Eof)   (return e (list eof s))]
       [(Var x) (interp-var e r s seen*)]
       [(Lam f xs e1)
        (return e (list (closure f xs e1 r) s))]       
       
       [(App e1 es)
        (match (interp-env* (cons e1 es) r s seen*)
          [(list as1 t1)
           (results-extend
            e t1
            (for/set ([a (in-set as1)])
              (match a
                [(list 'err s) (list 'err s)]
                [(list (cons v1 vs) s)
                 (apply-closure v1 vs s seen*)])))])]

       [(Prim0 p)
        (returns e (interp-prim0 p s))]

       [(Prim1 p e1)
        (match (interp-env e1 r s seen*)
          [(list as1 t1)
           (results-extend
            e t1
            (for/set ([a (in-set as1)])
              (match a
                [(list 'err s) (list (set (list 'err s)) (hasheq))]
                [(list v s)
                 (list (interp-prim1 e p v s) (hasheq))])))])]

       [(Prim2 p e1 e2)        
        (match (interp-env e1 r s seen*)
          [(list as1 t1)
           (results-extend
            e t1
            (for/set ([a1 (in-set as1)])
              (match a1
                [(list 'err s) (list (set (list 'err s)) (hasheq))]
                [(list v1 s)
                 (match (interp-env e2 r s seen*)
                   [(list as2 t2)
                    (results-extend
                     e t2
                     (for/set ([a2 (in-set as2)])
                       (match a2
                         [(list 'err s) (list (set (list 'err s)) (hasheq))]
                         [(list v2 s)
                          (list (interp-prim2 e p v1 v2 s) (hasheq))])))])])))])]                               

       [(Prim3 p e1 e2 e3)
        (match (interp-env e1 r s seen*)
          [(list as1 t1)
           (results-extend
            e t1
            (for/set ([a1 (in-set as1)])
              (match a1
                [(list 'err s) (list (set (list 'err s)) (hasheq))]
                [(list v1 s)
                 (match (interp-env e2 r s seen*)
                   [(list as2 t2)
                    (results-extend
                     e t2
                     (for/set ([a2 (in-set as2)])
                       (match a2
                         [(list 'err s) (list (set (list 'err s)) (hasheq))]
                         [(list v2 s)
                          (match (interp-env e3 r s seen*)
                            [(list as3 t3)
                             (results-extend
                              e t3
                              (for/set ([a3 (in-set as3)])
                                (match a3
                                  [(list 'err s) (list (set (list 'err s)) (hasheq))]
                                  [(list v3 s)
                                   (list (interp-prim3 e p v1 v2 v3 s) (hasheq))])))])])))])])))])]
       
       [(Begin e1 e2)
        (match (interp-env e1 r s seen*)
          [(list as1 t1)
           (results-extend
            e t1
            (for/set ([a (in-set as1)])
              (match a
                [(list 'err s) (list (set (list 'err s)) (hasheq))]
                [(list _ s)
                 (interp-env e2 r s seen*)])))])]

       [(If e1 e2 e3)
        (match (interp-env e1 r s seen*)
          [(list as1 t1)
           (results-extend
            e t1
            (for/set ([a1 (in-set as1)])
              (match a1
                [(list 'err s) (list (set (list 'err s)) (hasheq))]
                [(list v1 s)
                 (if (false? v1)
                     (interp-env e3 r s seen*)
                     (interp-env e2 r s seen*))])))])]

       [(Let x e1 e2)
        (match (interp-env e1 r s seen*)
          [(list as1 t1)
           (results-extend
            e t1
            (for/set ([a (in-set as1)])
              (match a
                [(list 'err s) (list (set (list 'err s)) (hasheq))]
                [(list v s)
                 (interp-env e2 (ext r x v) s seen*)])))])]

       
       ;[(Match e ps es) ...]
       )]))
            

;; Closure [Listof Value] Store Seen -> (list Answer Table)
(define (apply-closure f vs s seen)
  (match f
    [(closure _ xs e1 r)
     ; check arity matches
     (if (= (length xs) (length vs))
         (interp-env e1 (append (zip xs vs) r) s seen)
         (list (set (list 'err s)) (hasheq)))]))

(define current-abstract?
  (make-parameter #f))

;; Op0 Store -> (Setof Answer)
(define (interp-prim0 op s)
  (match op
    ['flip (set (list 0 s) (list 1 s))]
    ['read-byte (if (current-abstract?)
                    (set (list (Int) s) (list eof s))
                    (set (list (read-byte) s)))]
    ['peek-byte (if (current-abstract?)
                    (set (list (Int) s) (list eof s))
                    (set (list (peek-byte) s)))]
    ['void      (set (list (void) s))]))

;; Expr Op1 Value Store -> (Setof Answer)
(define (interp-prim1 e op v s)
  (match (list op v)
    [(list 'add1 (Int))                   (set (list (Int) s))]
    [(list 'add1 (? integer?))            (if (current-abstract?) (set (list (Int) s)) (set (list (add1 v) s)))]
    [(list 'sub1 (Int))                   (set (list (Int) s))]
    [(list 'sub1 (? integer?))            (if (current-abstract?) (set (list (Int) s)) (set (list (sub1 v) s)))]
    [(list 'zero? (Int))                  (set (list #t s) (list #f s))]
    [(list 'zero? (? integer?))           (set (list (zero? v) s))]
    [(list 'empty? v)                     (set (list (empty? v) s))]
    [(list 'char? (Char))                 (set (list #t s))]
    [(list 'char? (Int))                  (set (list #f s))]
    [(list 'char? v)                      (set (list (char? v) s))]
    [(list 'integer->char (Int))          (set (list (Char) s) (list 'err s))]
    [(list 'integer->char (Char))         (set (list 'err s))]
    [(list 'integer->char (? codepoint?)) (set (list (integer->char v) s))]
    [(list 'char->integer (Char))         (set (list (Int) s))]
    [(list 'char->integer (Int))          (set (list 'err s))]
    [(list 'char->integer (? char?))      (set (list (char->integer v) s))]
    [(list 'write-byte    (Int))          (set (list (void) s) (list 'err s))]
    [(list 'write-byte    (Char))         (set (list 'err s))]
    [(list 'write-byte    (? byte?))      (set (list (void) s))]
    [(list 'eof-object? (Int))            (set (list #f s))]
    [(list 'eof-object? (Char))           (set (list #f s))]
    [(list 'eof-object? v)                (set (list (eof-object? v) s))]
    [(list 'empty? v)                     (set (list (empty? v) s))]
    [(list 'cons? v)                      (set (list (cons-ptr? v) s))]
    [(list 'box? v)                       (set (list (box-ptr? v) s))]
    [(list 'vector? v)                    (set (list (vec-ptr? v) s))]
    [(list 'vector-length (vec-ptr a))
     (for/set ([v (hash-ref s a)])
       (cond [(vector? v)
              (list (vector-length v) s)]
             [(abs-vector? v)
              (list (Int) s)]))]
     
    #;[(list 'string? v)                    (string? v)]
    #;[(list 'string-length (? string?))    (string-length v)]
    [(list 'box v)
     (let ((a (if (current-abstract?)
                  e
                  (hash-count s))))
       
       (set (list (box-ptr a)
                  (hash-update s a
                               (λ (vs)
                                 (set-union vs (set (vector v))))
                               (set (vector v))))))]
    [(list 'unbox (box-ptr a))
     (for/set ([v (hash-ref s a)])     
       (list (vector-ref v 0) s))]
    [(list 'car (cons-ptr a))
     (for/set ([v (hash-ref s a)])
       (list (vector-ref v 0) s))]
    [(list 'cdr (cons-ptr a))
     (for/set ([v (hash-ref s a)])
       (list (vector-ref v 1) s))]
    [_ (set (list 'err s))]))

;; Expr Op2 Value Value -> (Setof Answer)
(define (interp-prim2 e op v1 v2 s)
  (match (list op v1 v2)
    [(list '+ (? integer?) (? integer?))
     (if (current-abstract?)
         (set (list (Int) s))
         (set (list (+ v1 v2) s)))]
    
    [(list '+ (or (? integer?) (Int)) (or (? integer?) (Int))) (set (list (Int) s))]
    [(list '- (? integer?) (? integer?)) (if (current-abstract?) (set (list (Int) s)) (set (list (- v1 v2) s)))]
    [(list '- (or (? integer?) (Int)) (or (? integer?) (Int))) (set (list (Int) s))]
    [(list '< (? integer?) (? integer?)) (set (list (< v1 v2) s))]
    [(list '< (or (? integer?) (Int)) (or (? integer?) (Int))) (set (list #t s) (list #f))]
    [(list '= (? integer?) (? integer?)) (set (list (= v1 v2) s))]
    [(list '= (or (? integer?) (Int)) (or (? integer?) (Int))) (set (list #t s) (list #f s))]
    [(list 'eq? (Abs) _) (set (list #t s) (list #f s))]
    [(list 'eq? _ (Abs)) (set (list #t s) (list #f s))]
    
    [(list 'eq? (cons-ptr a1) (cons-ptr a2))     
     (if (and (eq? a1 a2) (current-abstract?))
         (set (list #t s) (list #f s))
         (set (list (eq? a1 a2) s)))]
    
    [(list 'eq? (box-ptr a1) (box-ptr a2))
     (if (and (eq? a1 a2) (current-abstract?))
         (set (list #t s) (list #f s))
         (set (list (eq? a1 a2) s)))]
    
    [(list 'eq? v1 v2)   (set (list (eq? v1 v2) s))]
    
    ;[(list 'make-string (? integer?) (? char?)) ...]
    ;[(list 'string-ref (? string?) (? integer?)) ...]    
    [(list 'cons v1 v2)
     (let ((a (if (current-abstract?)
                  e
                  (hash-count s))))
       (set (list (cons-ptr a)
                  (hash-update s a
                               (λ (vs)
                                 (set-add vs (vector v1 v2)))
                               (set (vector v1 v2))))))]


    [(list 'make-vector (? nonnegative-integer? n) v)
     (let ((a (if (current-abstract?)
                  e
                  (hash-count s))))
       (set (list (vec-ptr a)
                  (hash-update s a
                               (λ (vs)
                                 (set-add vs (make-vector n v)))
                               (set (make-vector n v))))))]


    [(list 'make-vector (Int) v)
     (let ((a (if (current-abstract?)
                  e
                  (hash-count s))))
       (set (list (vec-ptr a)
                  (hash-update s a
                               (λ (vs)
                                 (set-add vs (abs-vector v)))
                               (set (abs-vector v))))))]

    [(list 'vector-ref (vec-ptr a) (? nonnegative-integer? i))
     (for/fold ([r (set)])
               ([v (hash-ref s a)])
       (cond [(vector? v)
              (if (< i (vector-length v))
                  (set-add r (list (vector-ref v i) s))
                  (set-add r (list 'err s)))]
             [(abs-vector? v)
              (set-union r
                         (set (list 'err s))
                         (set (list (abs-vector-v v) s)))]))]

    [(list 'vector-ref (vec-ptr a) (Int))
     (for/fold ([r (set (list 'err s))])
               ([v (hash-ref s a)])
       (set-union r
                  (cond [(vector? v)
                         (for/set ([i (vector-length v)])
                           (list (vector-ref v i) s))]
                        [(abs-vector? v)
                         (set (list (abs-vector-v v) s))])))]
         
    [_ (set (list 'err s))]))


;; Concrete:

;; [0 -> { #(#t) }]

;; (vector-set! (vec-ptr 0) 0 #f)

;; [0 -> { #(#f) }]

;; Abstract:

;; [a -> { #(#t) }]

;; (vector-set! (vec-ptr a) 0 #f)

;; [a -> { #(#t), #(#f) }]

;; [a0 -> { #(#t) }]
;; [a1 -> { #(#t) }]

;; (vector-set! (vec-ptr a) 0 #f)

;; [a0 -> { #(#f) }]
;; [a1 -> { #(#t) }]

;; or:

;; [a0 -> { #(#t) }]
;; [a1 -> { #(#f) }]

;; [a -> { #(#t), #(#f) }]

;; Expr Op3 Value Value Value -> (Setof Answer)
(define (interp-prim3 e op v1 v2 v3 s)
  (match (list op v1 v2 v3)
    [(list 'vector-set! (vec-ptr a) (? nonnegative-integer? i) v3)
     (for/fold ([r (set)])
               ([v (hash-ref s a)])
       (cond [(vector? v)
              (if (< i (vector-length v))
                  (set-add r
                           (list (void)
                                 (if (current-abstract?)
                                     (hash-set s a
                                               (set-add (hash-ref s a)
                                                        (vector-set v i v3)))
                                     (hash-set s a (set (vector-set v i v3))))))
                  (set-add r (list 'err s)))]
             [(abs-vector? v)
              (set-add (set-add r (list 'err s))
                       (list (void)
                             (hash-set s a (set-add (hash-ref s a) (abs-vector v3)))))]))]

    [(list 'vector-set! (vec-ptr a) (Int) v3)
     (for/fold ([r (set)])
               ([v (hash-ref s a)])
       (cond [(vector? v)
              (set-union r
                         (set (list 'err s))
                         (for/set ([i (vector-length v)])
                           (list (void)
                                 (if (current-abstract?)
                                     (hash-set s a
                                               (set-add (hash-ref s a)
                                                        (vector-set v i v3)))
                                     (hash-set s a (set (vector-set v i v3)))))))]

             [(abs-vector? v)
              (set-add (set-add r (list 'err s))                       
                       (list (void)
                             (hash-set s a (set-add (hash-ref s a) (abs-vector v3)))))]))]
       
    [_
     (set (list 'err s))]))

;; Function variant of vector-set!
(define (vector-set v i w)
  (let ((x (vector-copy v)))
    (begin (vector-set! x i w)
           x)))
  
;; Any -> Boolean
(define (codepoint? v)
  (and (integer? v)
       (or (<= 0 v 55295)
           (<= 57344 v 1114111))))

;; Table Expr -> (Setof Answer)
(define (table-lookup t e)
  (hash-ref t e (set)))

;; Table Expr (Setof Answer) -> Table
(define (table-extend t e a)
  (hash-update t e (λ (as) (set-union as a)) a))

(module+ test
  (let ((e (Var 'x)))
    (check-equal? (table-extend (hasheq) e (set 1))
                  (hasheq e (set 1)))
    (check-equal? (table-extend (hasheq e (set 1)) e (set 2))
                  (hasheq e (set 1 2)))))



;; Result Result -> Result
(define (result-join r1 r2)
  (match* (r1 r2)
    [((list as1 t1) (list as2 t2))
     (list (set-union as1 as2)
           (table-join t1 t2))]))

;; Result Table -> Result
(define (result-join-table r t)
  (match r
    [(list s t0) (list s (table-join t t0))]))

;; (Setof Result) -> Result
(define (results-join rs)
  (for/fold ([res (empty-result)])
            ([r (in-set rs)])
    (result-join res r)))


(module+ test
  (check-equal? (result-join (list (set) (hasheq)) (list (set) (hasheq)))
                (list (set) (hasheq)))
  (check-equal? (result-join (list (set 1) (hasheq)) (list (set 2) (hasheq)))
                (list (set 1 2) (hasheq)))
  (let ((e (Var 'x)))
    (check-equal? (result-join (list (set 1) (hasheq e (set 3)))
                               (list (set 2) (hasheq e (set 4))))
                  (list (set 1 2) (hasheq e (set 3 4))))))

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

;; Var Env Store Seen -> (list (Setof Answer) Table)
(define (interp-var e r s seen)
  (match e
    [(Var x)
     (match (lookup r x)
       ['err (list (set 'err) (hasheq e (set (list 'err s))))]
       [v (list (set (list v s)) (hasheq e (set (list v s))))])]))


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

;; [X -> Y] [Setof X] -> #t or #f
(define (set-findf f s)
  (for/or ([x (in-set s)])
    (f x)))

(define (err? x) (eq? x 'err))

(define (empty-result)
  (list (set) (hasheq)))

;; Answer -> Boolean
(define (truish? a)
  (match a
    ['err #f]
    [#f   #f]
    [_    #t]))

(define (set-filter f s)
  (for/set ([x (in-set s)]
            #:when (f x))
    x))



(define (type-integer? av)
  (andmap (λ (v) (or (integer? v) (Int? v) (err? v)))
          (set->list av)))

(define (type-proc? av)
  (andmap (λ (v) (or (closure? v) (err? v)))
          (set->list av)))

(define (known-lambda? av)
  (define ls (set-map (set-filter closure? av) closure-f))
  (match (set->list (list->set ls))
    [(list f) f]
    [_ #f]))