#lang racket

(define (f x y) 0)
(define (g x) 1)

((if (zero? (read-byte))
     f
     g)
 1 2)
