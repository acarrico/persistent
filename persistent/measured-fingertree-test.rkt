#lang racket

(require "measured-fingertree-sig.rkt")
(require "measured-fingertree-unit.rkt")
(require "measured-sig.rkt")

(require rackunit)

(define (measure-value x) 1)
(define mzero-value 0)

(define-values/invoke-unit
  measured-fingertree@
  (import (rename measured^
                  (+ mplus)
                  (mzero-value mzero)
                  (measure-value measure)))
  (export measured-fingertree^))

(check = 0 (measure (fingertree)))
(check = 1 (measure (push-left 'a (fingertree))))

(let-values (((a ft) (pop-left (push-left 'a (fingertree)))))
  (check eq? a 'a)
  (check-pred empty? ft))
;(check-pred single? (push-left 'a (fingertree)))
(check eq? 'a (first-left (push-left 'a (fingertree))))

(let ((ft (foldl push-left (fingertree) '(1 2 3 4 5 6))))
  (check equal?
         '(1 2 3 4 5 6)
         (reduce-left (lambda (a b) (cons b a)) '() ft))

  (check = 6 (measure ft))

  (check = 6 (first-left ft))
  (check = 5 (first-left (rest-left ft)))
  (check = 4 (first-left (rest-left (rest-left ft))))
  (check = 3 (first-left
              (rest-left (rest-left (rest-left ft)))))
  (check = 2 (first-left
              (rest-left
               (rest-left (rest-left (rest-left ft))))))
  (check = 1 (first-left
              (rest-left
               (rest-left
                (rest-left (rest-left (rest-left ft))))))))

(let-values (((ft a) (pop-right (push-right (fingertree) 'a))))
  (check eq? a 'a)
  (check-pred empty? ft))

(check eq? 'a (first-right (push-right (fingertree) 'a)))

(let ((ft (foldl (lambda (v ft) (push-right ft v)) (fingertree) '(1 2 3 4 5 6))))
  (check equal?
         '(1 2 3 4 5 6)
         (reduce-right cons ft '()))
  (check = 6 (first-right ft))
  (check = 5 (first-right (rest-right ft)))
  (check = 4 (first-right (rest-right (rest-right ft))))
  (check = 3 (first-right
              (rest-right (rest-right (rest-right ft)))))
  (check = 2 (first-right
              (rest-right
               (rest-right (rest-right (rest-right ft))))))
  (check = 1 (first-right
              (rest-right
               (rest-right
                (rest-right (rest-right (rest-right ft))))))))



(check equal? '(1 2 3 4 5) (fingertree->list (list->fingertree '(1 2 3 4 5))))
(check equal?
       '()
       (fingertree->list
        (concatenate
         (list->fingertree '())
         (list->fingertree '()))))
(check equal? '(1 2 3 4 5 a b c d e)
       (fingertree->list
        (concatenate
         (list->fingertree '(1 2 3 4 5))
         (list->fingertree '(a b c d e)))))

(let ((ft (list->fingertree '(1 2 3 4 5 6))))
  (split (lambda (x) (>= x 3)) 0 ft
         (lambda (left x right)
           (check equal? (fingertree->list left) '(1 2))
           (check = x 3)
           (check equal? (fingertree->list right) '(4 5 6)))
         (lambda (acc)
           (error "shouldn't be here")))

  (split (lambda (x) (> x 6)) 0 ft
         (lambda (left x right)
           (error "shouldn't be here"))
         (lambda (acc)
           (check = acc 6)))
  )
