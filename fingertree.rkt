#lang racket/base

(require racket/match)
(require unstable/custom-write)

(provide empty empty?
         reduce-left push-left pop-left first-left rest-left
         reduce-right push-right pop-right first-right rest-right
         list->fingertree fingertree->list concatenate)

(module+ test (require rackunit))

(struct digit1 (v0)
        #:property prop:custom-write
	(make-constructor-style-printer
	 (lambda (obj) 'digit)
	 (lambda (obj) (list (digit1-v0 obj)))))

(struct digit2 (v0 v1)
        #:property prop:custom-write
	(make-constructor-style-printer
	 (lambda (obj) 'digit)
	 (lambda (obj) (list (digit2-v0 obj) (digit2-v1 obj)))))

(struct digit3 (v0 v1 v2)
        #:property prop:custom-write
	(make-constructor-style-printer
	 (lambda (obj) 'digit)
	 (lambda (obj) (list (digit3-v0 obj) (digit3-v1 obj) (digit3-v2 obj)))))

(struct digit4 (v0 v1 v2 v3)
        #:property prop:custom-write
	(make-constructor-style-printer
	 (lambda (obj) 'digit)
	 (lambda (obj) (list (digit4-v0 obj) (digit4-v1 obj) (digit4-v2 obj) (digit4-v3 obj)))))

(define (digit-left d)
  (match d
    ((digit1 v0) v0)
    ((digit2 v0 v1) v0)
    ((digit3 v0 v1 v2) v0)
    ((digit4 v0 v1 v2 v3) v0)))

(define (digit-right d)
  (match d
    ((digit1 v0) v0)
    ((digit2 v0 v1) v1)
    ((digit3 v0 v1 v2) v2)
    ((digit4 v0 v1 v2 v3) v3)))

(struct node2 (v0 v1)
        #:property prop:custom-write
	(make-constructor-style-printer
	 (lambda (obj) 'node)
	 (lambda (obj) (list (node2-v0 obj) (node2-v1 obj)))))

(struct node3 (v0 v1 v2)
        #:property prop:custom-write
	(make-constructor-style-printer
	 (lambda (obj) 'node)
	 (lambda (obj) (list (node3-v0 obj) (node3-v1 obj) (node3-v2 obj)))))

(define (node->digit n)
  (match n
    ((node2 v0 v1) (digit2 v0 v1))
    ((node3 v0 v1 v2) (digit3 v0 v1 v2))))

;; fingertree: empty single or deep.
(struct empty ()
	#:property prop:custom-write
	(make-constructor-style-printer
	 (lambda (obj) 'empty)
	 (lambda (obj) (list))))

(struct single (v)
	#:property prop:custom-write
	(make-constructor-style-printer
	 (lambda (obj) 'single)
	 (lambda (obj) (list (single-v obj)))))

(struct deep (left spine right)
	#:property prop:custom-write
	(make-constructor-style-printer
	 (lambda (obj) 'deep)
	 (lambda (obj) (list (deep-left obj) (deep-spine obj) (deep-right obj)))))

;; (: push-left (all (a) (a (fingertree a) -> (fingertree a))))
;;
;; ISSUE: I'm not suspending the middle subtree of each Deep node:
;;
;; R. Hinze and R. Paterson:
;;
;; "Lazy evaluation is the norm in a language such as Haskell. In a strict
;; language that provides a lazy evaluation primitive, we need only
;; suspend the middle subtree of each Deep node, so only Θ(log n)
;; suspensions are required in a tree of size n. Even in a lazy language,
;; some space could be saved in practice by ensuring that these were the
;; only suspensions in the tree, for example by using Haskell’s
;; strictness annotations. Indeed we might wish to make the operations
;; even more strict, for example by forcing the middle subtree m in the
;; recursive case of ‘ ’ to avoid building a chain of
;; suspensions. According to the above debit analysis, this suspension
;; has been paid for by this time, so the amortized bounds would be
;; unaﬀected."
;;
;; One way to do this would be to add a second deep structure with a
;; suspended spine. Otherwise they could all have delayed spines to
;; take advantage of memoizing.

(define (digit-reduce-left fn z d)
  (match
    d
    ((digit1 v0) (fn z v0))
    ((digit2 v0 v1) (fn (fn z v0) v1))
    ((digit3 v0 v1 v2) (fn (fn (fn z v0) v1) v2))
    ((digit4 v0 v1 v2 v3) (fn (fn (fn (fn z v0) v1) v2) v3))
    (else
     (error "digit-reduce-left: malformed digit"))))

(define (node-reduce-left fn z n)
  (match
    n
    ((node2 v0 v1) (fn (fn z v0) v1))
    ((node3 v0 v1 v2) (fn (fn (fn z v0) v1) v2))
    (else
     (error "node-reduce-left: malformed node"))))

(define (reduce-left fn z ft)
  (match
    ft
    ((empty)
     z)
    ((single a)
     (fn z a))
    ((deep left spine right)
     (digit-reduce-left
      fn
      (reduce-left
       (lambda (z ft) (node-reduce-left fn z ft))
       (digit-reduce-left fn z left)
       spine)
      right))
    (else
     (error "reduce-left: malformed fingertree" ft))))

(define (push-left a ft)
  (match
   ft
   ((empty)
    (single a))
   ((single b)
    (deep (digit1 a) (empty) (digit1 b)))
   ((deep (digit1 b) spine right)
    (deep (digit2 a b) spine right))
   ((deep (digit2 b c) spine right)
    (deep (digit3 a b c) spine right))
   ((deep (digit3 b c d) spine right)
    (deep (digit4 a b c d) spine right))
   ((deep (digit4 b c d e) spine right)
    (deep (digit2 a b) (push-left (node3 c d e) spine) right))
   (else (error "push-left: malformed fingertree"))))

(define (pop-left ft)
  (match
   ft
   ((empty) (error "pop-left: empty"))
   ((single a) (values a (empty)))
   ((deep (digit1 a) spine right)
    (values
     a
     (if (empty? spine)
	 (match
           right
           ((digit1 b) (single b))
           ((digit2 b c) (deep (digit1 b) (empty) (digit1 c)))
           ((digit3 b c d) (deep (digit2 b c) (empty) (digit1 d)))
           ((digit4 b c d e) (deep (digit3 b c d) (empty) (digit1 e)))
           (else (error "pop-left: malformed fingertree")))
	 (let-values (((node spine) (pop-left spine)))
           (deep (node->digit node) spine right)))))
   ((deep (digit2 a b) spine right)
    (values a (deep (digit1 b) spine right)))
   ((deep (digit3 a b c) spine right)
    (values a (deep (digit2 b c) spine right)))
   ((deep (digit4 a b c d) spine right)
    (values a (deep (digit3 b c d) spine right)))
   (else
    (error "pop-left: malformed fingertree" ft))))

(define (first-left ft)
  (match
   ft
   ((empty) (error "first-left: empty"))
   ((single a) a)
   ((deep left spine right) (digit-left left))
   (else
    (error "first-left: malformed fingertree" ft))))

(define (rest-left ft)
  (define-values (_ result) (pop-left ft)) result)

(define (digit-reduce-right fn d z)
  (match
    d
    ((digit1 v0) (fn v0 z))
    ((digit2 v0 v1) (fn v0 (fn v1 z)))
    ((digit3 v0 v1 v2) (fn v0 (fn v1 (fn v2 z))))
    ((digit4 v0 v1 v2 v3) (fn v0 (fn v1 (fn v2 (fn v3 z)))))
    (else
     (error "digit-reduce-left: malformed digit"))))

(define (node-reduce-right fn n z)
  (match
    n
    ((node2 v0 v1) (fn v0 (fn v1 z)))
    ((node3 v0 v1 v2) (fn v0 (fn v1 (fn v2 z))))
    (else
     (error "node-reduce-left: malformed node"))))

(define (reduce-right fn ft z)
  (match
    ft
    ((empty)
     z)
    ((single a)
     (fn a z))
    ((deep left spine right)
     (digit-reduce-right
      fn
      left
      (reduce-right
       (lambda (ft z) (node-reduce-right fn ft z))
       spine
       (digit-reduce-right fn right z))))
    (else
     (error "reduce-right: malformed fingertree" ft))))

(define (push-right ft a)
  (match
   ft
   ((empty)
    (single a))
   ((single b)
    (deep (digit1 b) (empty) (digit1 a)))
   ((deep left spine (digit1 b))
    (deep left spine (digit2 b a)))
   ((deep left spine (digit2 c b))
    (deep left spine (digit3 c b a)))
   ((deep left spine (digit3 d c b))
    (deep left spine (digit4 d c b a)))
   ((deep left spine (digit4 e d c b))
    (deep left (push-right spine (node3 e d c)) (digit2 b a)))
   (else (error "push-right: malformed fingertree"))))

(define (pop-right ft)
  (match
   ft
   ((empty) (error "push-right: empty"))
   ((single a) (values (empty) a))
   ((deep left spine (digit1 a))
    (values
     (if (empty? spine)
	 (match
           left
           ((digit1 b) (single b))
           ((digit2 c b) (deep (digit1 c) (empty) (digit1 b)))
           ((digit3 d c b) (deep (digit1 d) (empty) (digit2 c b)))
           ((digit4 e d c b) (deep (digit1 e) (empty) (digit3 d c b)))
           (else (error "pop-right: malformed fingertree")))
	 (let-values (((spine node) (pop-right spine)))
           (deep left spine (node->digit node))))
     a))
   ((deep left spine (digit2 b a))
    (values (deep left spine (digit1 b)) a))
   ((deep left spine (digit3 c b a))
    (values (deep left spine (digit2 c b)) a))
   ((deep left spine (digit4 d c b a))
    (values (deep left spine (digit3 d c b)) a))
   (else
    (error "pop-right: malformed fingertree" ft))))

(define (first-right ft)
  (match
   ft
   ((empty) (error "first-right: empty"))
   ((single a) a)
   ((deep left spine right) (digit-right right))
   (else
    (error "first-right: malformed fingertree" ft))))

(define (rest-right ft)
  (define-values (result _) (pop-right ft)) result)

(module+
 test
 (let-values (((a ft) (pop-left (push-left 'a (empty)))))
   (check eq? a 'a)
   (check-pred empty? ft))
 (check-pred single? (push-left 'a (empty)))
 (check eq? 'a (first-left (push-left 'a (empty))))

 (let ((ft (foldl push-left (empty) '(1 2 3 4 5 6))))
   (check equal?
          '(1 2 3 4 5 6)
          (reduce-left (lambda (a b) (cons b a)) '() ft))

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

 (let-values (((ft a) (pop-right (push-right (empty) 'a))))
   (check eq? a 'a)
   (check-pred empty? ft))
 (check-pred single? (push-right (empty) 'a))
 (check eq? 'a (first-right (push-right (empty) 'a)))
 (let ((ft (foldl (lambda (v ft) (push-right ft v)) (empty) '(1 2 3 4 5 6))))
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
 )

(define (list->fingertree l)
  (foldl (lambda (x ft) (push-right ft x)) (empty) l))

(define (fingertree->list ft)
  (reduce-right cons ft '()))

(define (concatenate ft-x ft-y)
  (match (cons ft-x ft-y)
    ((cons (empty) _) ft-y)
    ((cons _ (empty)) ft-x)
    ((cons (single x) _) (push-left x ft-y))
    ((cons _ (single y)) (push-right ft-x y))
    ((cons (deep left-x spine-x right-x) (deep left-y spine-y right-y))
     (deep left-x
           ;; STRATEGY: push right-x and left-y into spine-x by 2's
           ;; and 3's then concatenate the two spines:
           (concatenate
            (match (cons right-x left-y)
              ;; 2
              ((cons (digit1 a) (digit1 b))
               (push-right spine-x (node2 a b)))
              ;; 3
              ((or (cons (digit2 a b) (digit1 c))
                   (cons (digit1 a) (digit2 b c))
                   )
               (push-right spine-x (node3 a b c)))
              ;; 4
              ((or (cons (digit3 a b c) (digit1 d))
                   (cons (digit2 a b) (digit2 c d))
                   (cons (digit1 a) (digit3 b c d))
                   )
               (push-right (push-right spine-x (node2 a b)) (node2 c d)))
              ;; 5
              ((or (cons (digit4 a b c d) (digit1 e))
                   (cons (digit3 a b c) (digit2 d e))
                   (cons (digit2 a b) (digit3 c d e))
                   (cons (digit1 a) (digit4 b c d e))
                   )
               (push-right (push-right spine-x (node3 a b c)) (node2 d e)))
              ;; 6
              ((or (cons (digit4 a b c d) (digit2 e f))
                   (cons (digit3 a b c) (digit3 d e f))
                   (cons (digit2 a b) (digit4 c d e f))
                   )
               (push-right (push-right spine-x (node3 a b c)) (node3 d e f)))
              ;; 7
              ((or (cons (digit4 a b c d) (digit3 e f g))
                   (cons (digit3 a b c) (digit4 d e f g)))
               (push-right (push-right (push-right spine-x (node3 a b c)) (node2 d e)) (node2 f g)))

              ((cons (digit4 a b c d) (digit4 e f g h))
               (push-right (push-right (push-right spine-x (node3 a b c)) (node3 d e f)) (node2 g h)))
              (else
               (error "concatenate: malformed fingertree(s)" ft-x ft-y)))
            spine-y)
           right-y))
    (else
     (error "concatenate: malformed fingertree(s)" ft-x ft-y))))

(module+
 test
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
 )
 
