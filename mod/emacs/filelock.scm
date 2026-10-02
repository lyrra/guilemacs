;;; filelock.scm --- M46 imp-2: the thin wrappers over the eight
;;;                    typed C leaves of src/filelock.c
;;;                    ((emacs filelock))
;;;
;;; The lockfile policy of src/filelock.c has eight parts: the lockfile
;;; name, the lock-info line, the boot-time read, the boot-time compare,
;;; the integer parse, the stale-owner parse, the clash loop, and the
;;; unlock policy (docs/m46-plan.org section 3.2).  M46 imp-2 adds one
;;; typed C leaf per part and this module of thin wrappers.  It moves no
;;; policy; imp-3 moves the choice into Scheme.
;;;
;;;   (filelock-lock-file-name fn)   -> a plain string, or #f.
;;;   (filelock-lock-info boot)      -> a plain string, or #f.
;;;   (filelock-boot-sec)            -> a plain integer.
;;;   (filelock-within-one-second a b) -> a plain boolean.
;;;   (filelock-integer-prefixed s)  -> a plain boolean.
;;;   (filelock-lock-owner lfname)   -> t when this process owns the
;;;                                     lock, a plain integer pid when
;;;                                     another process owns it, or #f
;;;                                     (free / stale / unreadable).
;;;   (filelock-lock-free-p lfname)  -> t (free or ours), a plain
;;;                                     integer owner pid (another
;;;                                     process), or #f on an error.
;;;   (filelock-unlock fn)           -> a plain boolean.
;;;
;;; Every value is plain: a string, an integer, a boolean, or #f.  No
;;; char *, no FILE *, no struct lock_info_type, and no Lisp_Object
;;; crosses the layer (the M42 rule).  The C leaf keeps the mechanism:
;;; link, symlink, mkostemp, rename, kill, readlinkat, and the
;;; struct lock_info_type buffer.
;;;
;;; This module holds no policy, no FFI call, and no raw syscall.  Each
;;; wrapper is a one-line call to its leaf.
;;;
;;; Conventions (identical to M9-M45): #nil is elisp nil; no
;;; module-level mutable state.

(define-module (emacs filelock)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (filelock-lock-file-name
            filelock-lock-info
            filelock-boot-sec
            filelock-within-one-second
            filelock-integer-prefixed
            filelock-lock-owner
            filelock-lock-free-p
            filelock-unlock))

;; The eight C leaves (src/filelock.c).
(defelisp %--filelock-lock-file-name      --filelock-lock-file-name)
(defelisp %--filelock-lock-info           --filelock-lock-info)
(defelisp %--filelock-boot-sec            --filelock-boot-sec)
(defelisp %--filelock-within-one-second   --filelock-within-one-second)
(defelisp %--filelock-integer-prefixed    --filelock-integer-prefixed)
(defelisp %--filelock-lock-owner          --filelock-lock-owner)
(defelisp %--filelock-lock-free-p         --filelock-lock-free-p)
(defelisp %--filelock-unlock              --filelock-unlock)

;; Return the encoded lock file name for FN, or #f when FN has no lock
;; file.  FN is a plain string.
(define (filelock-lock-file-name fn)
  ((force %--filelock-lock-file-name) fn))

;; Return the lock-info line (USER@HOST.PID:BOOT) as a plain string.
;; BOOT is a plain integer (from filelock-boot-sec), or 0.  #f on a bad
;; input.
(define (filelock-lock-info boot)
  ((force %--filelock-lock-info) boot))

;; Return the time of the last system boot as a plain integer, or 0.
(define (filelock-boot-sec)
  ((force %--filelock-boot-sec)))

;; Return t when the plain integers A and B are no more than one second
;; apart, else #f.
(define (filelock-within-one-second a b)
  ((force %--filelock-within-one-second) a b))

;; Return t when the plain string S starts with a decimal integer
;; (optionally negative), else #f.
(define (filelock-integer-prefixed s)
  ((force %--filelock-integer-prefixed) s))

;; Return t when this process owns the lock file LFNAME, a plain integer
;; pid when another process owns it, or #f for "free", "stale", and
;; "unreadable".
(define (filelock-lock-owner lfname)
  ((force %--filelock-lock-owner) lfname))

;; Return t when the lock named LFNAME is free or was zapped and is now
;; ours, a plain integer owner pid when another process owns it, or #f
;; on an error.
(define (filelock-lock-free-p lfname)
  ((force %--filelock-lock-free-p) lfname))

;; Return t when the lock for FN was removed or was not ours, else #f
;; when nothing was done.  The leaf does not report a file error.
(define (filelock-unlock fn)
  ((force %--filelock-unlock) fn))
