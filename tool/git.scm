;
; 1) install guile-git https://gitlab.com/guile-git/guile-git
;    $ ./configure --prefix=/home/you/guile
;
; 2) run:
;    guile -C /home/you/guile/lib/guile/3.0/site-ccache/ tool/git.scm -- -l
;
; Usage: [-l | -s] [-NUM] [ref]
; arguments:
; -l     -- each commit on a line
; -s     -- readable output
; -NUM   -- prints NUM number of commits
; ref    -- git commit ref
;
; examples:
; guile git.scm --          -- lists commits human readable
; guile git.scm -- -12      -- lists 12 first commits from head
; guile git.scm -- -s       -- lists commits machine readable
; guile git.scm -- -l       -- lists commits one-line mode
; guile git.scm -- cafebeef -- lists commits starting at tip cafebeef

(define-module (guilemacs-tool-git)
  #:use-module (ice-9 format)
  #:use-module (ice-9 match)
  #:use-module (git)
  ;#:use-module (git object)
  )

(libgit2-init!)

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

(define (loop-git-log commit stopn pfun)
  (when (or (not stopn) (> stopn 0))
    (pfun commit)
    ; cheating a bit: assumes single parent, and parent exists (ie not reaching root)
    (let ((parent (car (commit-parents commit))))
      (if parent
          (loop-git-log parent
                        (if stopn (1- stopn) #f)
                        pfun)))))

(define (run-git-log repository line-mode sexp stopnum ref)
  (let* ((oid (if ref
                  (object-id (object-lookup-prefix repository
                                                   (string->oid ref)
                                                   (string-length ref)))
                  (reference-target (repository-head repository))))
         (commit (commit-lookup repository oid)))
    (loop-git-log commit stopnum
                  (lambda (commit)
                    (print-commit commit line-mode sexp)))))

(let* ((directory "./")
       (repository (repository-open directory)))
  (let ((line-mode #f)
        (stopnum #f)
        (sexp #f)
        (ref #f))
    (for-each (lambda (arg)
                (cond
                 ((string=? "-l" arg) (set! line-mode arg))
                 ((string=? "-s" arg) (set! sexp arg))
                 ((char=? #\- (string-ref arg 0))
                  (if (char=? #\- (string-ref arg 0))
                      (set! stopnum (or stopnum
                                        (string->number (substring arg 1))))))
                 (else
                  (set! ref arg))))
              (cdr (command-line)))
    (run-git-log repository line-mode sexp stopnum ref)))

(libgit2-shutdown!)
