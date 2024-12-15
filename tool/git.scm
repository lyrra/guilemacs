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
  #:use-module (srfi srfi-171)
  #:use-module (rnrs io ports))

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

; expressing the generator as a fold would be cleaner,
; but we need to yield, so can't use standard srfi-1 fold,
; but would need a DSL that expresses fold as a generator
; that's why this looks so imperative,
; it's the result of that compilation
(define (commit-generator commit stopnum)
  (let ((current-commit commit))
    (lambda ()
      (if (and stopnum (<= stopnum 0))
          (eof-object)
          ; cheating a bit: assumes single parent, and parent exists (ie not reaching root)
          (let ((parent (car (commit-parents current-commit))))
            (if parent
                (begin
                  (if stopnum
                      (set! stopnum (1- stopnum)))
                  (let ((ret-commit current-commit))
                    (set! current-commit parent)
                    ret-commit))
                (eof-object)))))))

(define (print-commit-transducer line-mode sexp)
  (lambda (reducer)
    (lambda (result . commits)
      (if (null? commits)
          result
          (print-commit (car commits) line-mode sexp)))))

(define (get-commit-from-ref-or-name repo ref-or-name)
  (let ((iter (reference-iterator-glob-new repo (string-concatenate (list "refs/tags/" ref-or-name "*"))))
        (tag #f))
    (let ((ref (false-if-exception (reference-next iter))))
      (if ref
          (reference-name->oid repo
                               (reference-name ref))
          (object-id (object-lookup-prefix repo (string->oid ref-or-name)
                                           (string-length ref-or-name)))))))

(define (run-git-log repository line-mode sexp stopnum ref-or-name)
  (let* ((oid (if ref-or-name
                  (get-commit-from-ref-or-name repository ref-or-name)
                  (reference-target (repository-head repository))))
         (commit (commit-lookup repository oid)))
    (generator-transduce
     ; do side-effect during run of transducer
     (print-commit-transducer line-mode sexp)
     ; we dont collect anything, so dont build any result
     (lambda (x y) #f)
     #f
     (commit-generator commit stopnum))))

(define (run-git args)
  (libgit2-init!)
  (let* ((directory "./")
         (repository (repository-open directory)))
    (let ((line-mode #f)
          (stopnum #f)
          (sexp #f)
          (ref-or-name #f))
      (for-each (lambda (arg)
                  (cond
                   ((string=? "-l" arg) (set! line-mode arg))
                   ((string=? "-s" arg) (set! sexp arg))
                   ((char=? #\- (string-ref arg 0))
                    (if (char=? #\- (string-ref arg 0))
                        (set! stopnum (or stopnum
                                          (string->number (substring arg 1))))))
                   (else
                    (set! ref-or-name arg))))
                (cdr args))
      (run-git-log repository line-mode sexp stopnum ref-or-name)))
  (libgit2-shutdown!))

(run-git (command-line))
