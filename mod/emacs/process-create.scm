;;; process-create.scm --- M45 imp-2: the thin wrappers over the four
;;;                        typed C leaves of src/callproc.c
;;;                        ((emacs process-create))
;;;
;;; The parent-side process policy of src/callproc.c has four parts:
;;; the argument decode, the env block, the exec-path search, and the
;;; temp-file policy (docs/m45-plan.org section 3.3).  M45 imp-2 adds
;;; one typed C leaf per part and this module of thin wrappers.  It
;;; moves no policy; imp-3 moves the choice into Scheme.
;;;
;;;   (callproc-argv program args)  -> a plain list of strings, the
;;;                                    encoded argv with PROGRAM at the
;;;                                    head, or #f on a bad input.
;;;   (callproc-env current-dir)    -> a plain list of "NAME=VALUE"
;;;                                    strings, in the C order, or #f.
;;;   (callproc-resolve-program p)  -> the resolved path string after
;;;                                    the exec-path search, or #f.
;;;   (callproc-temp-name)          -> a plain (temp-dir pattern) list
;;;                                    of two strings.
;;;
;;; Every value is plain: a string, a list of strings, or #f.  No
;;; char **, no FILE *, no struct posix_spawn_*, and no Lisp_Object
;;; crosses the layer (the M42 rule).  The C leaf keeps the mechanism:
;;; fork, exec, posix_spawn, pipe, fcntl, dup2, mkostemp, and every
;;; char ** block.  A vfork child never enters the Guile VM, so
;;; child_setup and exec_failed stay C (the M44 pattern).
;;;
;;; This module holds no FFI call and no raw syscall.  It does not
;;; reuse (emacs process-accessors) or the other M39 / M40
;;; (emacs process-*) modules; it is a new sibling.
;;;
;;; Conventions (identical to M9-M44): #nil is elisp nil; no
;;; module-level mutable state.

(define-module (emacs process-create)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (callproc-argv
            callproc-env
            callproc-resolve-program
            callproc-temp-name))

;; The four C leaves (src/callproc.c).
(defelisp %--callproc-argv            --callproc-argv)
(defelisp %--callproc-env             --callproc-env)
(defelisp %--callproc-resolve-program --callproc-resolve-program)
(defelisp %--callproc-temp-name       --callproc-temp-name)

;; Return the argv as a plain list of strings, with PROGRAM at the head.
;; PROGRAM is the resolved program string (from callproc-resolve-program);
;; ARGS is the plain list of Elisp argument strings.  #f on a bad input.
(define (callproc-argv program args)
  ((force %--callproc-argv) program args))

;; Return the child environment as a plain list of "NAME=VALUE" strings.
;; CURRENT-DIR is a plain string.  #f on a bad input.
(define (callproc-env current-dir)
  ((force %--callproc-env) current-dir))

;; Return the resolved absolute path of PROGRAM, or #f when the
;; exec-path search fails.  The leaf does not report a file error.
(define (callproc-resolve-program program)
  ((force %--callproc-resolve-program) program))

;; Return a plain list (temp-dir pattern) of two strings for the
;; call-process-region temporary file.
(define (callproc-temp-name)
  ((force %--callproc-temp-name)))
