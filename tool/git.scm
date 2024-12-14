;
; 1) install guile-git https://gitlab.com/guile-git/guile-git
;    $ ./configure --prefix=/home/you/guile
;
; 2) run:
;    guile -C /home/you/guile/lib/guile/3.0/site-ccache/ tool/git.scm -- -l
;
;
; arguments:
; -l -- each commit on a line
; -s -- readable output
; -s<num> -- prints <num> number of commits

(define-module (guilemacs-tool-git))

(use-modules (ice-9 format)
             (ice-9 match))
(use-modules (git))

(libgit2-init!)

(define (loop-git-log commit stopn pfun)
  (pfun commit)
  ; cheating a bit: assumes single parent, and parent exists (ie not reaching root)
  (let ((parent (car (commit-parents commit))))
    (if (and parent (or (not stopn) (>= stopn 0)))
        (loop-git-log parent
                      (if stopn (1- stopn) #f)
                      pfun))))

(define (print-commit commit line-mode sexp)
  (let ((id (substring (oid->string (commit-id commit)) 0 8)))
    (cond
     (line-mode
      (let* ((msg (string-delete (lambda (c)
                                   (char=? #\Newline c))
                                 (commit-message commit)))
             (msg (substring msg 0 (min (string-length msg) 30))))
        (format #t "commit ~a ~a~%" id msg)))
     (sexp
      (format #t "(commit ~s ~s)~%" id (commit-message commit)))
     (else
      (format #t ";-------------------------------------------~%")
      (format #t "commit ~a~%" id)
      (format #t "~%~a~%" (commit-message commit))
      (format #t "~%")))))

(define (run-git-log repository line-mode sexp stopnum)
  (let* ((oid (reference-target (repository-head repository)))
         (commit (commit-lookup repository oid)))
    (loop-git-log commit stopnum
                  (lambda (commit)
                    (print-commit commit line-mode sexp)))))

(let* ((directory "./")
       (repository (repository-open directory)))
  (let ((line-mode #f)
        (stopnum #f)
        (sexp #f))
    (for-each (lambda (arg)
                (cond
                 ((string=? "-l" arg) (set! line-mode arg))
                 ((string=? "-s" arg) (set! sexp arg))
                 (else
                  (when (char=? #\- (string-ref arg 0))
                    (set! stopnum (or stopnum
                                      (string->number (substring arg 1))))))))
              (command-line))
    (run-git-log repository line-mode sexp stopnum)))

(libgit2-shutdown!)
