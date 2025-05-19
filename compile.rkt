#lang racket
(provide compile
         compile-e
         compile-es
         ;compile-define
         compile-match
         compile-match-clause
         compile-lambda-define
         compile-string ; for notes
         copy-env-to-stack
         free-vars-to-heap)

(require "ast.rkt")
(require "compile-ops.rkt")
(require "types.rkt")
(require "lambdas.rkt")
(require "fv.rkt")
(require "finterp.rkt")
(require a86/ast)

(define rax 'rax)
(define rbx 'rbx) ; heap
(define rsp 'rsp) ; stack
(define rdi 'rdi) ; arg
(define r8  'r8)  ; scratch
(define r9  'r9)  ; scratch
(define r15 'r15) ; stack pad (non-volatile)

(define rbp 'rbp)

;; Prog -> Asm
(define (compile p)
  (define t (analyze p))
  (match p
    [(Prog ds e)
     (prog (Global 'entry)
           (Extern 'peek_byte)
           (Extern 'read_byte)
           (Extern 'write_byte)
           (Extern 'raise_error)
           (Extern 'collect_garbage)
           (Label 'entry)
           (Push rbx)    ; save callee-saved registers
           (Push rbp)
           (Push r15)
           (Mov rbp rsp) ; save stack base pointer
           (Mov rbx rdi) ; recv heap pointer
           (compile-defines-values ds)
           (compile-e e (reverse (define-ids ds)) #f t)
           (Add rsp (* 8 (length ds))) ;; pop function definitions
           (Pop r15)     ; restore callee-save registers
           (Pop rbp)
           (Pop rbx)
           (Ret)
           (compile-defines ds t)
           (compile-lambda-defines (lambdas p) t)
           (Label 'err)
           pad-stack
           (Call 'raise_error))]))

;; [Listof Lam] -> [Listof Id]
(define (define-ids ds)
  (match ds
    ['() '()]
    [(cons (Lam f xs e) ds)
     (cons f (define-ids ds))]))

;; [Listof Lam] Table -> Asm
(define (compile-defines ds t)
  (match ds
    ['() (seq)]
    [(cons d ds)
     (seq (compile-lambda-define d t)
          (compile-defines ds t))]))

;; [Listof Lam] Table -> Asm
(define (compile-lambda-defines ls t)
  (match ls
    ['() (seq)]
    [(cons l ls)
     (seq (compile-lambda-define l t)
          (compile-lambda-defines ls t))]))


;; Table -> (Setof App)
;; Produce all of the applications used in the table
(define (applications t)  
  (for/fold ((s (set)))
            ((e (hash-keys t)))
    (match e
      [(App e0 es) (set-union s (set e))]
      [_ s])))

;; Lam Table -> (Setof App)
(define (callers l t)
  (for/fold ((s (set)))
            ((e (applications t)))
    (match e
      [(App e0 es)
       (if (has-closure? (hash-ref t e0) l)
           (set-union s (set e))
           s)])))

;; Lam Table -> (Setof Integer)
(define (caller-arities l t)
  (for/set ((e (callers l t)))
    (match e
      [(App e0 es) (length es)])))



(define (has-closure? s l)
  (match l
    [(Lam l xs e)
     (for/or ((v (in-set s)))
       (match v
         [(closure l0 _ _ _) (eq? l l0)]
         [_ #f]))]))

       
    

    


;; Lam Table -> Asm
(define (compile-lambda-define l t)
  (let ((fvs (fv l)))
    (match l
      [(Lam f xs e)
       (let ((env  (append (reverse fvs) (reverse xs) (list #f))))
         (seq (Dq (length fvs))
              (Label (symbol->label f))


              (if (equal? (set (length xs))
                          (caller-arities l t))
                  (% "omit arity check")
                  (seq 
                   (% "arity check")
                   (Cmp r15 (length xs))
                   (Jne 'err)))
              
              (Mov rax (Offset rsp (* 8 (length xs))))
              (copy-env-to-stack fvs 8)
              (compile-e e env #t t)
              (Add rsp (* 8 (length env))) ; pop env
              (Ret)))])))

;; [Listof Id] Int -> Asm
;; Copy the closure environment at given offset to stack
(define (copy-env-to-stack fvs off)
  (match fvs
    ['() (seq)]
    [(cons _ fvs)
     (seq (Mov r9 (Offset rax (- off type-proc)))
          (Push r9)
          (copy-env-to-stack fvs (+ 8 off)))]))

;; type CEnv = (Listof [Maybe Id])
;; Expr CEnv Boolean Table -> Asm
(define (compile-e e c t? t)
  (match e
    [(Lit d) (compile-value d)]
    [(Eof) (compile-value eof)]
    [(Var x) (compile-variable x c)]
    [(Prim0 p) (compile-prim0 p)]
    [(Prim1 p e) (compile-prim1 p e c t)]
    [(Prim2 p e1 e2) (compile-prim2 p e1 e2 c t)]
    [(Prim3 p e1 e2 e3) (compile-prim3 p e1 e2 e3 c t)]
    [(If e1 e2 e3)
     (compile-if e1 e2 e3 c t? t)]
    [(Begin e1 e2)
     (compile-begin e1 e2 c t? t)]
    [(Let x e1 e2)
     (compile-let x e1 e2 c t? t)]
    [(App e es)
     (compile-app e es c t? t)]
    [(Lam f xs e)
     (compile-lam f xs e c)]
    [(Match e ps es) (compile-match e ps es c t?)]))

;; Value -> Asm
(define (compile-value v)
  (cond [(string? v) (compile-string v)]
        [else        (Mov rax (value->bits v))]))

;; Id CEnv -> Asm
(define (compile-variable x c)
  (let ((i (lookup x c)))
    (seq (Mov rax (Offset rsp i)))))

;; String -> Asm
(define (compile-string s)
  (let ((len (string-length s)))
    (if (zero? len)
        (seq (Mov rax type-str))
        (seq (Mov rax len)
             (Mov (Offset rbx 0) rax)
             (compile-string-chars (string->list s) 8)
             (Mov rax rbx)
             (Xor rax type-str)
             (Add rbx
                  (+ 8 (* 4 (if (odd? len) (add1 len) len))))))))

;; [Listof Char] Integer -> Asm
(define (compile-string-chars cs i)
  (match cs
    ['() (seq)]
    [(cons c cs)
     (seq (Mov rax (char->integer c))
          (Mov (Offset rbx i) 'eax)
          (compile-string-chars cs (+ 4 i)))]))

;; Op0 -> Asm
(define (compile-prim0 p)
  (compile-op0 p))

;; Op1 Expr CEnv Table -> Asm
(define (compile-prim1 p e c t)
  (seq (compile-e e c #f t)
       (compile-op1 p (hash-ref t e))))

;; Op2 Expr Expr CEnv Table -> Asm
(define (compile-prim2 p e1 e2 c t)
  (seq (compile-e e1 c #f t)
       (Push rax)
       (compile-e e2 (cons #f c) #f t)
       (compile-op2 p)))

;; Op3 Expr Expr Expr CEnv Table -> Asm
(define (compile-prim3 p e1 e2 e3 c t)
  (seq (compile-e e1 c #f t)
       (Push rax)
       (compile-e e2 (cons #f c) #f t)
       (Push rax)
       (compile-e e3 (cons #f (cons #f c)) #f t)
       (compile-op3 p)))

;; Expr Expr Expr CEnv Boolean Table -> Asm
(define (compile-if e1 e2 e3 c t? t)
  (let ((l1 (gensym 'if))
        (l2 (gensym 'if)))
    (seq (compile-e e1 c #f t)
         (Cmp rax (value->bits #f))
         (Je l1)
         (compile-e e2 c t? t)
         (Jmp l2)
         (Label l1)
         (compile-e e3 c t? t)
         (Label l2))))

;; Expr Expr CEnv Boolean Table -> Asm
(define (compile-begin e1 e2 c t? t)
  (seq (compile-e e1 c #f t)
       (compile-e e2 c t? t)))


;; Id Expr Expr CEnv Boolean Table -> Asm
(define (compile-let x e1 e2 c t? t)
  (seq (compile-e e1 c #f t)
       (Push rax)
       (compile-e e2 (cons x c) t? t)
       (Add rsp 8)))

;; Id [Listof Expr] CEnv Table -> Asm
;; The return address is placed above the arguments, so callee pops
;; arguments and return address is next frame
;; Expr [Listof Expr] CEnv Boolean -> Asm
(define (compile-app e es c t? t)
  (if t?
      (compile-app-tail e es c t)
      (compile-app-nontail e es c t)))

;; Expr [Listof Expr] CEnv Table -> Asm
(define (compile-app-tail e es c t)
  (seq (compile-es (cons e es) c t)
       (move-args (add1 (length es)) (length c))
       (Add rsp (* 8 (length c)))
       (Mov rax (Offset rsp (* 8 (length es))))
       (if (type-proc? (hash-ref t e))
           (% "Skipped proc type check")
           (assert-proc rax))

       (% "Pass arity info")
       (Mov r15 (length es))
       
       (let ((l (known-lambda? (hash-ref t e))))
         (if l
             (seq (%% "Known lambda")
                  (Jmp (symbol->label l)))
             (seq (Mov rax (Offset rax (- type-proc)))
                  (Jmp rax))))))

;; Integer Integer -> Asm
(define (move-args i off)
  (cond [(zero? off) (seq)]
        [(zero? i)   (seq)]
        [else
         (seq (Mov r8 (Offset rsp (* 8 (sub1 i))))
              (Mov (Offset rsp (* 8 (+ off (sub1 i)))) r8)
              (move-args (sub1 i) off))]))

;; Expr [Listof Expr] CEnv Table -> Asm
;; The return address is placed above the arguments, so callee pops
;; arguments and return address is next frame
(define (compile-app-nontail e es c t)
  (let ((r (gensym 'ret))
        (i (* 8 (length es))))
    (seq (Lea rax r)
         (Push rax)
         (compile-es (cons e es) (cons #f c) t)
         (Mov rax (Offset rsp i))
         (if (type-proc? (hash-ref t e))
             (%% "Skipped proc type check")
             (assert-proc rax))

         (% "Pass arity info")
         (Mov r15 (length es))
       
         (let ((l (known-lambda? (hash-ref t e))))
           (if l
               (seq (%% "Known lambda")
                    (Jmp (symbol->label l)))
               (seq (Mov rax (Offset rax (- type-proc)))
                    (Jmp rax))))
         
         (Label r))))

;; [Listof Lam] -> Asm
;; Compile the closures for ds and push them on the stack
(define (compile-defines-values ds)
  (seq (alloc-defines ds 0)
       (init-defines ds (reverse (define-ids ds)) 8)
       (add-rbx-defines ds 0)))

;; [Listof Lam] Int -> Asm
;; Allocate closures for ds at given offset, but don't write environment yet
(define (alloc-defines ds off)
  (match ds
    ['() (seq)]
    [(cons (and (Lam f xs e) l) ds)
     (let ((fvs (fv l)))
       (seq (Lea rax (symbol->label f))
            (Mov (Offset rbx off) rax)
            (Mov rax rbx)
            (Add rax off)
            (Xor rax type-proc)
            (Push rax)
            (alloc-defines ds (+ off (* 8 (add1 (length fvs)))))))]))

;; [Listof Lam] CEnv Int -> Asm
;; Initialize the environment for each closure for ds at given offset
(define (init-defines ds c off)
  (match ds
    ['() (seq)]
    [(cons l ds)
     (let ((fvs (fv l)))
       (seq (free-vars-to-heap fvs c off)
            (init-defines ds c (+ off (* 8 (add1 (length fvs)))))))]))

;; [Listof Lam] Int -> Asm
;; Compute adjustment to rbx for allocation of all ds
(define (add-rbx-defines ds n)
  (match ds
    ['() (seq (Add rbx (* n 8)))]
    [(cons l ds)
     (add-rbx-defines ds (+ n (add1 (length (fv l)))))]))

;; Id [Listof Id] Expr CEnv -> Asm
(define (compile-lam f xs e c)
  (let ((fvs (fv (Lam f xs e))))
    (seq (Lea rax (symbol->label f))
         (Mov (Offset rbx 0) rax)
         (free-vars-to-heap fvs c 8)
         (Mov rax rbx) ; return value
         (Xor rax type-proc)
         (Add rbx (* 8 (add1 (length fvs)))))))

;; [Listof Id] CEnv Int -> Asm
;; Copy the values of given free variables into the heap at given offset
(define (free-vars-to-heap fvs c off)
  (match fvs
    ['() (seq)]
    [(cons x fvs)
     (seq (Mov r8 (Offset rsp (lookup x c)))
          (Mov (Offset rbx off) r8)
          (free-vars-to-heap fvs c (+ off 8)))]))

;; [Listof Expr] CEnv Table -> Asm
(define (compile-es es c t)
  (match es
    ['() '()]
    [(cons e es)
     (seq (compile-e e c #f t)
          (Push rax)
          (compile-es es (cons #f c) t))]))

;; Expr [Listof Pat] [Listof Expr] CEnv Bool -> Asm
(define (compile-match e ps es c t?)
  (let ((done (gensym)))
    (seq (compile-e e c #f)
         (Push rax) ; save away to be restored by each clause
         (compile-match-clauses ps es (cons #f c) done t?)
         (Jmp 'err)
         (Label done)
         (Add rsp 8)))) ; pop the saved value being matched

;; [Listof Pat] [Listof Expr] CEnv Symbol Bool -> Asm
(define (compile-match-clauses ps es c done t?)
  (match* (ps es)
    [('() '()) (seq)]
    [((cons p ps) (cons e es))
     (seq (compile-match-clause p e c done t?)
          (compile-match-clauses ps es c done t?))]))

;; Pat Expr CEnv Symbol Bool -> Asm
(define (compile-match-clause p e c done t?)
  (let ((next (gensym)))
    (match (compile-pattern p '() next)
      [(list i cm)
       (seq (Mov rax (Offset rsp 0)) ; restore value being matched
            i
            (compile-e e (append cm c) t?)
            (Add rsp (* 8 (length cm)))
            (Jmp done)
            (Label next))])))

;; Pat CEnv Symbol -> (list Asm CEnv)
(define (compile-pattern p cm next)
  (match p
    [(Var '_)
     (list (seq) cm)]
    [(Var x)
     (list (seq (Push rax)) (cons x cm))]
    [(Lit l)
     (let ((ok (gensym)))
       (list (seq (Mov r8 rax)
                  (compile-value l)
                  (Cmp rax r8)
                  (Je ok)
                  (Add rsp (* 8 (length cm)))
                  (Jmp next)
                  (Label ok))
             cm))]
    [(Conj p1 p2)
     (match (compile-pattern p1 (cons #f cm) next)
       [(list i1 cm1)
        (match (compile-pattern p2 cm1 next)
          [(list i2 cm2)
           (list
            (seq (Push rax)
                 i1
                 (Mov rax (Offset rsp (* 8 (- (sub1 (length cm1)) (length cm)))))
                 i2)
            cm2)])])]
    [(Box p)
     (match (compile-pattern p cm next)
       [(list i1 cm1)
        (let ((ok (gensym)))
          (list
           (seq (Mov r8 rax)
                (And r8 ptr-mask)
                (Cmp r8 type-box)
                (Je ok)
                (Add rsp (* 8 (length cm))) ; haven't pushed anything yet
                (Jmp next)
                (Label ok)
                (Mov rax (Offset rax (- type-box)))
                i1)
           cm1))])]
    [(Cons p1 p2)
     (match (compile-pattern p1 (cons #f cm) next)
       [(list i1 cm1)
        (match (compile-pattern p2 cm1 next)
          [(list i2 cm2)
           (let ((ok (gensym)))
             (list
              (seq (Mov r8 rax)
                   (And r8 ptr-mask)
                   (Cmp r8 type-cons)
                   (Je ok)
                   (Add rsp (* 8 (length cm))) ; haven't pushed anything yet
                   (Jmp next)
                   (Label ok)
                   (Xor rax type-cons)
                   (Mov r8 (Offset rax 0))
                   (Push r8)                ; push cdr
                   (Mov rax (Offset rax 8)) ; mov rax car
                   i1
                   (Mov rax (Offset rsp (* 8 (- (sub1 (length cm1)) (length cm)))))
                   i2)
              cm2))])])]))

;; Id CEnv -> Integer
(define (lookup x cenv)
  (match cenv
    ['() (error "undefined variable:" x)]
    [(cons y rest)
     (match (eq? x y)
       [#t 0]
       [#f (+ 8 (lookup x rest))])]))

