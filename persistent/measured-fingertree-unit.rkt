#lang racket/unit

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

(require "measured-fingertree-sig.rkt")
(require "measured-sig.rkt")
(require racket/match)
(require unstable/custom-write)

(import measured^)
(export (rename measured-fingertree^ (measure-export measure)))

(define (measure-export ft)
  (measure-fingertree measure ft))

(define (mplus3 a b c) (mplus (mplus a b) c))
(define (mplus4 a b c d) (mplus (mplus a b) (mplus c d)))

;; NOTE: an empty digit never shows up in a fingertree, but it is
;; useful when splitting up digits:
(struct digit0 ()
        #:property prop:custom-write
        (make-constructor-style-printer
         (lambda (obj) 'digit0)
         (lambda (obj) '())))

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

(define (left-digit d)
  (match d
    ((digit1 v0) v0)
    ((digit2 v0 v1) v0)
    ((digit3 v0 v1 v2) v0)
    ((digit4 v0 v1 v2 v3) v0)))

(define (right-digit d)
  (match d
    ((digit1 v0) v0)
    ((digit2 v0 v1) v1)
    ((digit3 v0 v1 v2) v2)
    ((digit4 v0 v1 v2 v3) v3)))

(define (measure-digit measure d)
  (match d
    ((digit1 v0) (measure v0))
    ((digit2 v0 v1) (mplus (measure v0) (measure v1)))
    ((digit3 v0 v1 v2)
     (mplus3 (measure v0) (measure v1) (measure v2)))
    ((digit4 v0 v1 v2 v3)
     (mplus4 (measure v0) (measure v1) (measure v2) (measure v3)))))

(struct node2 (cache v0 v1)
        #:property prop:custom-write
        (make-constructor-style-printer
         (lambda (obj) 'node)
         (lambda (obj) (list (node2-cache obj) ': (node2-v0 obj) (node2-v1 obj)))))

(define (make-node2 measure v0 v1)
  (node2 (mplus (measure v0) (measure v1)) v0 v1))

(struct node3 (cache v0 v1 v2)
        #:property prop:custom-write
        (make-constructor-style-printer
         (lambda (obj) 'node)
         (lambda (obj) (list (node3-cache obj) ': (node3-v0 obj) (node3-v1 obj) (node3-v2 obj)))))

(define (make-node3 measure v0 v1 v2)
  (node3 (mplus3 (measure v0) (measure v1) (measure v2)) v0 v1 v2))

(define (node-cache n)
  (match n
    ((struct node2 _) (node2-cache n))
    ((struct node3 _) (node3-cache n))
    (else
     (error "node-cache: malformed node" n))))

(define (node->digit n)
  (match n
    ((node2 cache v0 v1) (digit2 v0 v1))
    ((node3 cache v0 v1 v2) (digit3 v0 v1 v2))))

;; fingertree: empty single or deep.
(struct empty ()
        #:property prop:custom-write
        (make-constructor-style-printer
         (lambda (obj) 'empty)
         (lambda (obj) (list))))

(define fingertree empty)

(struct single (v)
        #:property prop:custom-write
        (make-constructor-style-printer
         (lambda (obj) 'single)
         (lambda (obj) (list (single-v obj)))))

(struct deep (cache left spine right)
        #:property prop:custom-write
        (make-constructor-style-printer
         (lambda (obj) 'deep)
         (lambda (obj) (list (deep-cache obj) ': (deep-left obj) (deep-spine obj) (deep-right obj)))))

(define (make-deep measure left spine right)
  (deep (mplus3 (measure-digit measure left)
                (measure-fingertree node-cache spine)
                (measure-digit measure right))
        left spine right))

(define (make-deep/empty-digits measure left spine right)
  (cond ((empty? spine)
         (match (cons left right)
           ((cons (digit0) (digit0))
            (empty))
           ((cons (digit0) (digit1 a))
            (single a))
           ((cons (digit0) (digit2 a b))
            (make-deep measure (digit1 a) (empty) (digit1 b)))
           ((cons (digit0) (digit3 a b c))
            (make-deep measure (digit2 a b) (empty) (digit1 c)))
           ((cons (digit0) (digit4 a b c d))
            (make-deep measure (digit2 a b c) (empty) (digit1 d)))
           ((cons (digit1 a) (digit0))
            (single a))
           ((cons (digit2 a b) (digit0))
            (make-deep measure (digit1 a) (empty) (digit1 b)))
           ((cons (digit3 a b c) (digit0))
            (make-deep measure (digit2 a b) (empty) (digit1 c)))
           ((cons (digit4 a b c d) (digit0))
            (make-deep measure (digit2 a b c) (empty) (digit1 d)))
           (else
            (make-deep measure left spine right))))
        ((digit0? left)
         (let-values (((node spine) (pop-left-fingertree node-cache spine)))
           (make-deep measure (node->digit node) spine right)))
        ((digit0? right)
         (let-values (((spine node) (pop-right-fingertree node-cache spine)))
           (make-deep measure left spine (node->digit node))))
        (else
          (make-deep measure left spine right))))

(define (measure-fingertree measure ft)
  (match ft
    ((empty) mzero)
    ((single v) (measure v))
    ((struct deep _) (deep-cache ft))))

(define (reduce-left-digit fn z d)
  (match
    d
    ((digit1 v0) (fn z v0))
    ((digit2 v0 v1) (fn (fn z v0) v1))
    ((digit3 v0 v1 v2) (fn (fn (fn z v0) v1) v2))
    ((digit4 v0 v1 v2 v3) (fn (fn (fn (fn z v0) v1) v2) v3))
    (else
     (error "reduce-left-digit: malformed digit"))))

(define (reduce-left-node fn z n)
  (match
    n
    ((node2 _ v0 v1) (fn (fn z v0) v1))
    ((node3 _ v0 v1 v2) (fn (fn (fn z v0) v1) v2))
    (else
     (error "reduce-left-node: malformed node"))))

(define (reduce-left fn z ft)
  (match
    ft
    ((empty)
     z)
    ((single a)
     (fn z a))
    ((deep _ left spine right)
     (reduce-left-digit
      fn
      (reduce-left
       (lambda (z ft) (reduce-left-node fn z ft))
       (reduce-left-digit fn z left)
       spine)
      right))
    (else
     (error "reduce-left: malformed fingertree" ft))))

(define (push-left a ft)
  (push-left-fingertree measure a ft))

(define (push-left-fingertree measure a ft)
  (match
    ft
    ((empty)
     (single a))
    ((single b)
     (make-deep measure (digit1 a) (empty) (digit1 b)))
    ((deep _ (digit1 b) spine right)
     (make-deep measure (digit2 a b) spine right))
    ((deep _ (digit2 b c) spine right)
     (make-deep measure (digit3 a b c) spine right))
    ((deep _ (digit3 b c d) spine right)
     (make-deep measure (digit4 a b c d) spine right))
    ((deep _ (digit4 b c d e) spine right)
     (make-deep measure
                (digit2 a b)
                (push-left-fingertree node-cache (make-node3 measure c d e) spine)
                right))
    (else (error "push-left-fingertree: malformed fingertree"))))

(define (pop-left ft)
  (pop-left-fingertree measure ft))

(define (pop-left-fingertree measure ft)
  (match
    ft
    ((empty) (error "pop-left-fingertree: empty"))
    ((single a) (values a (empty)))
    ((deep _ (digit1 a) spine right)
     (values a (make-deep/empty-digits measure (digit0) spine right)))
    ((deep _ (digit2 a b) spine right)
     (values a (make-deep measure (digit1 b) spine right)))
    ((deep _ (digit3 a b c) spine right)
     (values a (make-deep measure (digit2 b c) spine right)))
    ((deep _ (digit4 a b c d) spine right)
     (values a (make-deep measure (digit3 b c d) spine right)))
    (else
     (error "pop-left-fingertree: malformed fingertree" ft))))

(define (first-left ft)
  (match
    ft
    ((empty) (error "first-left: empty"))
    ((single a) a)
    ((deep _ left spine right) (left-digit left))
    (else
     (error "first-left: malformed fingertree" ft))))

(define (rest-left ft)
  (define-values (_ result) (pop-left ft)) result)

(define (reduce-right-digit fn d z)
  (match
    d
    ((digit1 v0) (fn v0 z))
    ((digit2 v0 v1) (fn v0 (fn v1 z)))
    ((digit3 v0 v1 v2) (fn v0 (fn v1 (fn v2 z))))
    ((digit4 v0 v1 v2 v3) (fn v0 (fn v1 (fn v2 (fn v3 z)))))
    (else
     (error "reduce-left-digit: malformed digit"))))

(define (reduce-right-node fn n z)
  (match
    n
    ((node2 _ v0 v1) (fn v0 (fn v1 z)))
    ((node3 _ v0 v1 v2) (fn v0 (fn v1 (fn v2 z))))
    (else
     (error "reduce-left-node: malformed node"))))

(define (reduce-right fn ft z)
  (match
    ft
    ((empty)
     z)
    ((single a)
     (fn a z))
    ((deep _ left spine right)
     (reduce-right-digit
      fn
      left
      (reduce-right
       (lambda (ft z) (reduce-right-node fn ft z))
       spine
       (reduce-right-digit fn right z))))
    (else
     (error "reduce-right: malformed fingertree" ft))))

(define (push-right ft a)
  (push-right-fingertree measure ft a))

(define (push-right-fingertree measure ft a)
  (match
    ft
    ((empty)
     (single a))
    ((single b)
     (make-deep measure (digit1 b) (empty) (digit1 a)))
    ((deep _ left spine (digit1 b))
     (make-deep measure left spine (digit2 b a)))
    ((deep _ left spine (digit2 c b))
     (make-deep measure left spine (digit3 c b a)))
    ((deep _ left spine (digit3 d c b))
     (make-deep measure left spine (digit4 d c b a)))
    ((deep _ left spine (digit4 e d c b))
     (make-deep measure
                left
                (push-right-fingertree node-cache spine (make-node3 measure e d c))
                (digit2 b a)))
    (else (error "push-right-fingertree: malformed fingertree"))))

(define (pop-right ft)
  (pop-right-fingertree measure ft))

(define (pop-right-fingertree measure ft)
  (match
   ft
   ((empty) (error "push-right-fingertree: empty"))
   ((single a) (values (empty) a))
   ((deep _ left spine (digit1 a))
    (values (make-deep/empty-digits measure left spine (digit0)) a))
   ((deep _ left spine (digit2 b a))
    (values (make-deep measure left spine (digit1 b)) a))
   ((deep _ left spine (digit3 c b a))
    (values (make-deep measure left spine (digit2 c b)) a))
   ((deep _ left spine (digit4 d c b a))
    (values (make-deep measure left spine (digit3 d c b)) a))
   (else
    (error "pop-right-fingertree: malformed fingertree" ft))))

(define (first-right ft)
  (match
    ft
    ((empty) (error "first-right: empty"))
    ((single a) a)
    ((deep _ left spine right) (right-digit right))
    (else
     (error "first-right: malformed fingertree" ft))))

(define (rest-right ft)
  (define-values (result _) (pop-right ft)) result)

(define (list->fingertree l)
  (foldl (lambda (x ft) (push-right ft x)) (empty) l))

(define (fingertree->list ft)
  (reduce-right cons ft '()))

(define (concatenate ft-x ft-y)
  (concatenate-fingertree measure ft-x ft-y))

(define (concatenate-fingertree measure ft-x ft-y)
  (match (cons ft-x ft-y)
    ((cons (empty) _) ft-y)
    ((cons _ (empty)) ft-x)
    ((cons (single x) _) (push-left-fingertree measure x ft-y))
    ((cons _ (single y)) (push-right-fingertree measure ft-x y))
    ((cons (deep _ left-x spine-x right-x) (deep _ left-y spine-y right-y))
     (make-deep
      measure
      left-x
      ;; STRATEGY: push right-x and left-y into spine-x by 2's
      ;; and 3's then concatenate the two spines:
      (concatenate-fingertree
       node-cache
       (match (cons right-x left-y)
         ;; 2
         ((cons (digit1 a) (digit1 b))
          (push-right-fingertree node-cache spine-x (make-node2 measure a b)))
         ;; 3
         ((or (cons (digit2 a b) (digit1 c))
              (cons (digit1 a) (digit2 b c)))
          (push-right-fingertree node-cache spine-x (make-node3 measure a b c)))
         ;; 4
         ((or (cons (digit3 a b c) (digit1 d))
              (cons (digit2 a b) (digit2 c d))
              (cons (digit1 a) (digit3 b c d)))
          (push-right-fingertree
           node-cache
           (push-right-fingertree node-cache spine-x (make-node2 measure a b))
           (make-node2 measure c d)))
         ;; 5
         ((or (cons (digit4 a b c d) (digit1 e))
              (cons (digit3 a b c) (digit2 d e))
              (cons (digit2 a b) (digit3 c d e))
              (cons (digit1 a) (digit4 b c d e))
              )
          (push-right-fingertree
           node-cache
           (push-right-fingertree node-cache spine-x (make-node3 measure a b c))
           (make-node2 measure d e)))
         ;; 6
         ((or (cons (digit4 a b c d) (digit2 e f))
              (cons (digit3 a b c) (digit3 d e f))
              (cons (digit2 a b) (digit4 c d e f)))
          (push-right-fingertree
           node-cache
           (push-right-fingertree node-cache spine-x (make-node3 measure a b c))
           (make-node3 measure d e f)))
         ;; 7
         ((or (cons (digit4 a b c d) (digit3 e f g))
              (cons (digit3 a b c) (digit4 d e f g)))
          (push-right-fingertree
           node-cache
           (push-right-fingertree
            node-cache
            (push-right-fingertree
             node-cache spine-x (make-node3 measure a b c))
            (node2 measure d e))
           (make-node2 measure f g)))
         ;; 8
         ((cons (digit4 a b c d) (digit4 e f g h))
          (push-right-fingertree
           node-cache
           (push-right-fingertree
            node-cache
            (push-right-fingertree
             node-cache
             spine-x (make-node3 measure a b c))
            (make-node3 measure d e f))
           (make-node2 measure g h)))
         (else
          (error "concatenate: malformed fingertree(s)" ft-x ft-y)))
       spine-y)
      right-y))
    (else
     (error "concatenate: malformed fingertree(s)" ft-x ft-y))))

(define (split-digit measure pred acc d
                     split-k
                     false-k)
  (match d
    ((digit1 v0)
     (let ((acc (mplus acc (measure v0))))
       (if (pred acc)
           (split-k (digit0) v0 (digit0))
           (false-k acc))))
    ((digit2 v0 v1)
     (let ((acc (mplus acc (measure v0))))
       (if (pred acc)
           (split-k (digit0) v0 (digit1 v1))
           (let ((acc (mplus acc (measure v1))))
             (if (pred acc)
                 (split-k (digit1 v0) v1 (digit0))
                 (false-k acc))))))
    ((digit3 v0 v1 v2)
     (let ((acc (mplus acc (measure v0))))
       (if (pred acc)
           (split-k (digit0) v0 (digit2 v1 v2))
           (let ((acc (mplus acc (measure v1))))
             (if (pred acc)
                 (split-k (digit1 v0) v1 (digit1 v2))
                 (let ((acc (mplus acc (measure v2))))
                   (if (pred acc)
                       (split-k (digit2 v0 v1) v2 (digit0))
                       (false-k acc))))))))
    ((digit4 v0 v1 v2 v3)
     (let ((acc (mplus acc (measure v0))))
       (if (pred acc)
           (split-k (digit0) v0 (digit3 v1 v2 v3))
           (let ((acc (mplus acc (measure v1))))
             (if (pred acc)
                 (split-k (digit1 v0) v1 (digit2 v2 v3))
                 (let ((acc (mplus acc (measure v2))))
                   (if (pred acc)
                       (split-k (digit2 v0 v1) v2 (digit1 v3))
                       (let ((acc (mplus acc (measure v3))))
                         (if (pred acc)
                             (split-k (digit3 v0 v1 v2) v3 (digit0))
                             (false-k acc))))))))))
    (else
     (error "split-digit: malformed digit" d))))

(define (digit->fingertree measure d)
  (match d
    ((digit0) (empty))
    ((digit1 v0) (single v0))
    ((digit2 v0 v1) (make-deep measure (digit1 v0) (empty) (digit1 v1)))
    ((digit3 v0 v1 v2) (make-deep measure (digit2 v0 v1) (empty) (digit1 v2)))
    ((digit4 v0 v1 v2 v3) (make-deep measure (digit3 v0 v1 v2) (empty) (digit1 v3)))
    (else
     (error "digit->fingertree not a digit" d))))

(define (split pred acc ft split-k false-k)
  (split-fingertree measure pred acc ft split-k false-k))

(define (split-fingertree measure pred acc ft split-k false-k)

  (define (split-left left spine right)
    (split-digit
     measure pred acc left
     (lambda (left-split v right-split)
       (split-k (digit->fingertree measure left-split)
                v
                (make-deep/empty-digits measure right-split spine right)))
     (lambda (acc)
       (split-spine left acc spine right))))

  (define (split-spine left acc spine right)
    (split-fingertree
     node-cache pred acc spine
     (lambda (left-split split-node right-split)
       (let ((acc (mplus acc (measure-fingertree node-cache left-split))))
         (match split-node
           ((node2 _ a b)
            (let ((acc (mplus acc (measure a))))
              (if (pred acc)
                  (split-k
                   (make-deep/empty-digits measure left left-split (digit0))
                   a
                   (make-deep measure (digit1 b) right-split right))
                  (split-k
                   (make-deep measure left left-split (digit1 a))
                   b
                   (make-deep/empty-digits measure (digit0) right-split right)))))
           ((node3 _ a b c)
            (let ((acc (mplus acc (measure a))))
              (if (pred acc)
                  (split-k
                   (make-deep/empty-digits measure left left-split (digit0))
                   a
                   (make-deep/empty-digits measure (digit1 b c) right-split right))
                  (let ((acc (mplus acc (measure b))))
                    (if (pred acc)
                        (split-k
                         (make-deep measure left left-split (digit1 a))
                         b
                         (make-deep measure (digit1 c) right-split right))
                        (split-k
                         (make-deep measure left left-split (digit2 a b))
                         c
                         (make-deep/empty-digits measure (digit0) right-split right)))))))
           (else
            (error "split-fingertree: malformed fingertree")))))
     (lambda (acc)
       (split-right acc left spine right))))

  (define (split-right acc left spine right)
    (split-digit
     measure pred acc right
     (lambda (left-split v right-split)
       (split-k (make-deep/empty-digits measure left spine left-split)
                v
                (digit->fingertree measure right-split)))
     (lambda (acc)
       (false-k acc))))

  (match ft
    ((empty) (false-k acc))
    ((single v)
     (let ((acc (mplus acc (measure v))))
       (if (pred acc)
           (split-k (empty) v (empty))
           (false-k acc))))
    ((deep _ left spine right)
     (split-left left spine right))))
