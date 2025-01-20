(define-module (utils)
  #:use-module (srfi srfi-1)
  #:export (randomize-list))

(define (%randomize-list lst acc)
  (if (null? lst)
      acc
      (let* ((len (length lst))
             (n (random len)))
        (%randomize-list (fold (lambda (a b acc)
                                 (if (= n b)
                                     acc
                                     (cons a acc)))
                               '() lst (iota len))
                         (cons (list-ref lst n) acc)))))

(define (randomize-list lst)
  (%randomize-list lst '()))
