#lang racket
(require "ast.rkt")

(module+ test (require rackunit))

(struct closure (xs e r) #:transparent)

(struct Abs () #:transparent)
(struct Int Abs () #:transparent)
(struct Char Abs () #:transparent)

;(define (f x) (add1 x))
;(list (f 1) (f 2))

;; type Answer = Value | 'err

;; type Value =  ...
;;            | (Int) | (Char)

;; type Env = (Listof (List Id Value))

;; type Table = (Hashof Expr (Setof Answer))

;; Prog -> (list (Setof Answer) Table)
(define (interp p)
  (match p
    [(Prog ds e)
     (interp-env e '() ds (set))]))

;; type Result = (list (Setof Answer) Table)


(define (result-extend e t0 r)
  (match r
    [(list as t)
     (list as (table-extend (table-join t0 t) e as))]))

(define (return e a)
  (returns e (set a)))

(define (returns e as)
  (list as (hasheq e as)))

;; [Listof Expr] Env Defns Seen ->  (list (Listof (Setof Answer)) Table)
(define (interp-env* es r ds seen)
  (match es
    ['() (list '() (hasheq))]
    [(cons e es)
     (match (interp-env e r ds seen)
       [(list as t)
        (match (interp-env* es r ds seen)
          [(list as* t*)
           (list (cons as as*) (table-join t t*))])])]))
     
;; [Setof Closure] [Listof [Setof Value]] Defns Seen -> Result
(define (apply-closures fs vss ds seen)
  (for*/fold ([r (empty-result)])
             ([f (in-set fs)]
              [vs (in-set (args-list vss))])
    (result-join r
                 (apply-closure f vs ds seen))))
    


; (f {1 2} {3 4})
; (list {1 2} {3 4})
; (apply-closure f '(1 3))
; (apply-closure f '(1 4))
; ...

;; [Listof [Setof Value]] -> [Setof [Listof Value]]
(define (args-list vs)
  (match vs
    ['() (set '())]
    [(cons vs vss)
     (for*/fold ([s (set)])
                ([l (in-set (args-list vss))]
                 [v (in-set vs)])
       (set-add s (cons v l)))]))

(module+ test
  (check-equal? (args-list '()) (set '()))
  (check-equal? (args-list (list (set 1 2) (set 3 4)))
                (set (list 1 3)
                     (list 1 4)
                     (list 2 3)
                     (list 2 4))))


(define (value? a)
  (match a
    ['err #f]
    [_ #t]))

;; type Seen = (Setof (list Expr Env))

;; Expr Env Defns Seen -> Result
(define (interp-env e r ds seen)
  (cond
    [(set-member? seen (list e r))
     (list (set) (hasheq e (set)))]
    [else
     (define seen* (set-add seen (list e r)))
     (match e
       [(Lit d) (return e d)]
       [(Var x) (interp-var e r ds seen*)]
       [(Lam f xs e1)
        (return e (closure xs e1 r))]
       
       
       [(App e1 es)
        (match (interp-env e1 r ds seen*)
          [(list as1 t1)
           (match (interp-env* es r ds seen*) ; (list (Listof (Setof Answer)) Table)
             [(list as t)
              (result-extend e (table-join t1 t)
                             (apply-closures (set-filter closure? as1)
                                             (map (λ (an) (set-filter value? an)) as)
                                             ds
                                             seen*))])])]
        
        
       [(Prim0 p)
        (returns e (interp-prim0 p))]
        
       [(Prim1 p e1)
        (match (interp-env e1 r ds seen*)
          [(list as1 t1)
           (result-extend e t1
                          (list (set-union
                                 (if (set-member? as1 'err)
                                     (set 'err)
                                     (set))
                                 (interp-prim1s p (set-filter (negate err?) as1)))
                                (hasheq)))])]
        
       [(Prim2 p e1 e2)
        (match (interp-env e1 r ds seen*)
          [(list as1 t1)
           (match (interp-env e2 r ds seen*)
             [(list as2 t2)
              (result-extend e (table-join t1 t2)
                             (list (interp-prim2s p as1 as2) (hasheq)))])])]
        
        
        
        
        
       [(Begin e1 e2)
        (match (interp-env e1 r ds seen*)
          [(list as1 t1)
           (result-extend e t1
                          (result-join         
                           (if (set-member? as1 'err)
                               (list (set 'err) (hasheq))
                               (list (set) (hasheq)))
                           (if (set-findf (negate err?) as1)
                               (interp-env e2 r ds seen*)             
                               (empty-result))))])]
        
        
       [(If e1 e2 e3)
        (match (interp-env e1 r ds seen*)
          [(list as1 t1)
           (result-extend e t1
                          (result-join
                           (if (set-member? as1 'err)
                               (list (set 'err) (hasheq))
                               (empty-result))
                           (result-join
                            (if (set-findf false? as1)
                                (interp-env e3 r ds seen*)
                                (empty-result))
                            (if (set-findf truish? as1)
                                (interp-env e2 r ds seen*)
                                (empty-result)))))])])]))                                              
  
  
  
  
  
;; Closure [Listof Value] Defns Seen -> (list Answer Table)
(define (apply-closure f vs ds seen)
  (match f
    [(closure xs e1 r)
     ; check arity matches
     (if (= (length xs) (length vs))
         (interp-env e1 (append (zip xs vs) r) ds seen)
         (list 'err (hasheq)))]))

#;
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



;; Op0 -> (Setof Answer)
(define (interp-prim0 op)
  (match op
    ['read-byte (set (Int) eof) #;(set (read-byte))]
    ['peek-byte (set (Int) eof) #;(set (peek-byte))]
    ['void      (set (void))]))

;; Op1 Value -> (Setof Answer)
(define (interp-prim1 op v)
  (match (list op v)
    [(list 'add1 (Int))                   (set (Int))]
    [(list 'add1 (? integer?))            #;(set (add1 v)) (set (Int))]
    [(list 'sub1 (Int))                   (set (Int))]
    [(list 'sub1 (? integer?))            #;(set (sub1 v)) (set (Int))]
    [(list 'zero? (Int))                  (set #t #f)]
    [(list 'zero? (? integer?))           (set (zero? v))]
    [(list 'char? (Char))                 (set #t)]
    [(list 'char? (Int))                  (set #f)]
    [(list 'char? v)                      (set (char? v))]
    [(list 'integer->char (Int))          (set (Char) 'err)]
    [(list 'integer->char (Char))         (set 'err)]
    [(list 'integer->char (? codepoint?)) (set (integer->char v))]
    [(list 'char->integer (Char))         (set (Int))]
    [(list 'char->integer (Int))          (set 'err)]
    [(list 'char->integer (? char?))      (char->integer v)]
    [(list 'write-byte    (Int))          (set (void) 'err)]
    [(list 'write-byte    (Char))         (set 'err)]
    [(list 'write-byte    (? byte?))      (set (void))]
    [(list 'eof-object? (Int))            (set #f)]
    [(list 'eof-object? (Char))           (set #f)]
    [(list 'eof-object? v)                (set (eof-object? v))]
    [_ (set 'err)]))

;; Op2 Value Value -> (Setof Answer)
(define (interp-prim2 op v1 v2)
  (match (list op v1 v2)
    [(list '+ (? integer?) (? integer?)) #;(set (+ v1 v2)) (set (Int))]
    [(list '+ (or (? integer?) (Int)) (or (? integer?) (Int))) (set (Int))]
    [(list '- (? integer?) (? integer?)) #;(set (- v1 v2)) (set (Int))]
    [(list '- (or (? integer?) (Int)) (or (? integer?) (Int))) (set (Int))]
    [(list '< (? integer?) (? integer?)) (set (< v1 v2))]
    [(list '< (or (? integer?) (Int)) (or (? integer?) (Int))) (set #t #f)]
    [(list '= (? integer?) (? integer?)) (set (= v1 v2))]
    [(list '= (or (? integer?) (Int)) (or (? integer?) (Int))) (set #t #f)]
    [_ (set 'err)]))







(define (interp-prim1s op vs)
  (for/fold ([s (set)])
            ([v (in-set vs)])
    (set-union s (interp-prim1 op v))))

(define (interp-prim2s op vs1 vs2)
  (for*/fold [(s (set))]
             ([v1 (in-set vs1)]
              [v2 (in-set vs2)])
    (set-union s (interp-prim2 op v1 v2))))
             

         
;; Any -> Boolean
(define (codepoint? v)
  (and (integer? v)
       (or (<= 0 v 55295)
           (<= 57344 v 1114111))))

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

;; Var Env [Listof Defn] Seen -> (list (Setof Answer) Table)
(define (interp-var e r ds seen)
  (match e
    [(Var x)
     (match (lookup r x)
       ['err (match (defns-lookup ds x)
               [(Defn f xs e) (interp-env (Lam f xs e) '() ds seen)]
               [#f (list (set 'err) (hasheq e (set 'err)))])]
       [v (list (set v) (hasheq e (set v)))])]))

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
    
