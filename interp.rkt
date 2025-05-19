#lang racket
(provide interp)
(provide interp-env)
(provide interp-match-pat)
(require "ast.rkt")
(require "interp-prim.rkt")
(require "env.rkt")

;; type Value =
;; | Integer
;; | Boolean
;; | Character
;; | Eof
;; | Void
;; | '()
;; | (cons Value Value)
;; | (box Value)
;; | (string Character ...)
;; | (vector Value ...)
;; | (Value ... -> Answer)

;; type Answer = Value | 'err

;; type Env = (Listof (List Id Value))

(struct nope ())

;; Prog -> Answer | nope
(define (interp p)
  (match p
    [(Prog ds e)
     (interp-env e '() ds 1000)]))

;; Expr Env Defns Nat -> Answer | nope
(define (interp-env e r ds i)
  (if (zero? i)
      (nope)      
      (match e
        [(Lit d) d]
        [(Eof)   eof]
        [(Var x) (interp-var x r ds i)]
        [(Prim0 'read-byte) (nope)]
        [(Prim0 'peek-byte) (nope)]    
        [(Prim0 p) (interp-prim0 p)]    
        [(Prim1 'write-byte e) (nope)]
        [(Prim1 p e)
         (match (interp-env e r ds (sub1 i))
           ['err 'err]
           [(nope) (nope)]
           [v (interp-prim1 p v)])]
        [(Prim2 p e1 e2)
         (match (interp-env e1 r ds (sub1 i))
           ['err 'err]
           [(nope) (nope)]
           [v1 (match (interp-env e2 r ds (sub1 i))
                 ['err 'err]
                 [(nope) (nope)]
                 [v2 (interp-prim2 p v1 v2)])])]
        [(Prim3 p e1 e2 e3)
         (match (interp-env e1 r ds (sub1 i))
           ['err 'err]
           [(nope) (nope)]
           [v1 (match (interp-env e2 r ds (sub1 i))
                 ['err 'err]
                 [(nope) (nope)]
                 [v2 (match (interp-env e3 r ds (sub1 i))
                       ['err 'err]
                       [(nope) (nope)]
                       [v3 (interp-prim3 p v1 v2 v3)])])])]
        [(If e0 e1 e2)
         (match (interp-env e0 r ds (sub1 i))
           [(nope) (nope)]
           ['err 'err]
           [v
            (if v
                (interp-env e1 r ds (sub1 i))
                (interp-env e2 r ds (sub1 i)))])]
        [(Begin e1 e2)
         (match (interp-env e1 r ds (sub1 i))
           ['err 'err]
           [(nope) (nope)]
           [v    (interp-env e2 r ds (sub1 i))])]
        [(Let x e1 e2)
         (match (interp-env e1 r ds (sub1 i))
           ['err 'err]
           [(nope) (nope)]
           [v (interp-env e2 (ext r x v) ds (sub1 i))])]
        [(App e es)
         (match (interp-env e r ds (sub1 i))
           ['err 'err]
           [(nope) (nope)]
           [f
            (match (interp-env* es r ds (sub1 i))
              ['err 'err]
              [(nope) (nope)]
              [vs
               (if (procedure? f)
                   (apply f vs)
                   'err)])])]
        [(Match e ps es)
         (match (interp-env e r ds (sub1 i))
           [(nope) (nope)]
           ['err 'err]
           [v
            (interp-match v ps es r ds (sub1 i))])]
        [(Lam f xs e)
         (λ vs
           ; check arity matches
           (if (= (length xs) (length vs))
               (interp-env e (append (zip xs vs) r) ds (sub1 i))
               'err))])))

;; (Listof Expr) REnv Defns Nat -> (Listof Value) | 'err | nope
(define (interp-env* es r ds i)
  (match es
    ['() '()]
    [(cons e es)
     (match (interp-env e r ds (sub1 i))
       ['err 'err]
       [(nope) (nope)]
       [v (match (interp-env* es r ds i)
            ['err 'err]
            [vs (cons v vs)])])]))

;; Id Env [Listof Defn] -> Answer
(define (interp-var x r ds i)
  (match (lookup r x)
    ['err (match (defns-lookup ds x)
            [(Defn f xs e) (interp-env (Lam f xs e) '() ds (sub1 i))]
            [#f 'err])]
    [v v]))

;; Value [Listof Pat] [Listof Expr] Env Defns Nat -> Answer
(define (interp-match v ps es r ds i)
  (match* (ps es)
    [('() '()) 'err]
    [((cons p ps) (cons e es))
     (match (interp-match-pat p v r)
       [#f (interp-match v ps es r ds)]
       [r  (interp-env e r ds)])]))

;; Pat Value Env -> [Maybe Env]
(define (interp-match-pat p v r)
  (match p
    [(Var '_) r]
    [(Var x) (ext r x v)]
    [(Lit l) (and (eqv? l v) r)]
    [(Box p)
     (match v
       [(box v)
        (interp-match-pat p v r)]
       [_ #f])]
    [(Cons p1 p2)
     (match v
       [(cons v1 v2)
        (match (interp-match-pat p1 v1 r)
          [#f #f]
          [r1 (interp-match-pat p2 v2 r1)])]
       [_ #f])]
    [(Conj p1 p2)
     (match (interp-match-pat p1 v r)
       [#f #f]
       [r1 (interp-match-pat p2 v r1)])]))

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

