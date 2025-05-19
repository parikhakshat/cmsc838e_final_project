#lang racket

(define (f n a)
  (if (zero? n)
      a
      (f (sub1 n) (add1 a))))

(f 1000000 0)

