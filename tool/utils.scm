(define-module (utils)
  #:use-module (srfi srfi-1)
  #:export (push! push-append! randomize-list
            string-remove-substr
            print-report-table))

(define-syntax push!
  (syntax-rules ()
    ((_ lst item)
     (set! lst (cons item lst)))))

(define-syntax push-append!
  (syntax-rules ()
    ((_ lst lst2)
     (set! lst (append lst lst2)))))

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

(define (string-remove-substr str sub)
  (let ((n (string-contains str sub)))
    (if n
        (string-concatenate (list (substring str 0 n)
                                  (substring str (+ (string-length sub) 1))))
        #f)))

(define (leftpad str len)
  (string-concatenate
   (list (make-string len #\Space)
         str)))

(define (print-report-table tab)
  (let* ((tab (map (lambda (row)
                     (map (lambda (col)
                            (if col
                                (format #f "~a" col)
                                ""))
                          row))
                   tab))
         (numcols (length (car tab)))
         (collen (apply map (lambda cols
                              (apply max (map string-length cols)))
                        tab)))
    (let ((print-row (lambda (row . plus)
                       (for-each (lambda (col len)
                                   (format #t "~a~a" (leftpad col
                                                              (- len (string-length col)))
                                           (if (null? plus) " | " "-+-")))
                                 row collen)
                       (format #t "~%"))))
      (print-row (car tab))
      (print-row (map (lambda (len) (make-string len #\-)) collen) #f)
      (for-each print-row
                (cdr tab)))))
