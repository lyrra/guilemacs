;;; fileio.scm --- M34 imp-3: the fileio.c safe_run_hooks caller
;;;               M47 imp-2: the thin wrappers over the 26 typed C
;;;               file-I/O leaves
;;;               ((emacs fileio))
;;;
;;; M34 imp-3 moved the *decision* logic of the live src/fileio.c call
;;; site of the safe_run_hooks stub into Scheme.  The *mechanism* stays
;;; C: the do_auto_save message push, the quit-flag save and restore, and
;;; the auto_save_unwind.  See brief.org 4.
;;;
;;; M47 imp-2 grows this module with one thin wrapper per typed C leaf of
;;; src/fileio.c (brief.org section 5 and section 7).  Each leaf returns
;;; *plain values only* (a string, an integer, a boolean, a list, or #f).
;;; imp-2 moves no policy; imp-3 … imp-5 rewire the C hubs onto these
;;; wrappers.  The wrapper name is the *contract*: imp-3 … imp-5 look it
;;; up with (scm_c_public_ref "emacs fileio" "fileio-<block>").
;;;
;;; This module holds no policy, no FFI call, and no raw syscall.  Each
;;; wrapper is a one-line call to its leaf.
;;;
;;; Conventions (identical to M9-M46, cf. mod/emacs/filelock.scm):
;;; cross-module targets are resolved lazily with delay + module-ref; #f
;;; is elisp nil; no module-level mutable state.

(define-module (emacs fileio)
  #:use-module (emacs elisp-ref)      ; defelisp
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (fileio-run-auto-save-hook!
            ;; M47 imp-2 -- G1, the file-name / path policy
            fileio-find-file-name-handler
            fileio-file-name-directory
            fileio-file-name-nondirectory
            fileio-file-name-as-directory
            fileio-directory-file-name
            fileio-file-name-concat
            fileio-expand-file-name
            fileio-substitute-in-file-name
            ;; M47 imp-2 -- G2, the OS-query predicate policy
            fileio-file-exists-p
            fileio-file-executable-p
            fileio-file-readable-p
            fileio-file-writable-p
            fileio-access-file
            fileio-file-symlink-p
            fileio-file-directory-p
            fileio-file-regular-p
            fileio-file-modes
            fileio-file-newer-than-file-p
            fileio-file-system-info
            ;; M47 imp-2 -- G3, the copy / rename / link / delete policy
            fileio-copy-file
            fileio-make-directory-internal
            fileio-delete-directory-internal
            fileio-delete-file-internal
            fileio-rename-file
            fileio-add-name-to-file
            fileio-make-symbolic-link))

;; (emacs command-loop) holds the safe_run_hooks port.  Resolve it lazily,
;; so the module does not eagerly import (emacs command-loop).  See
;; brief.org 4.
(define %safe-run-hooks!
  (delay (module-ref (resolve-module '(emacs command-loop))
                     'safe-run-hooks!)))

;;; --- fileio-run-auto-save-hook! ------------------------------------
;;; Port of the site call in do_auto_save (src/fileio.c):
;;;   hook = Qauto_save_hook;
;;;   safe_run_hooks (hook);
;;; It takes no argument.  Call (emacs command-loop) safe-run-hooks! on the
;;; auto-save-hook symbol.  Return nothing.  See brief.org 4.
(define (fileio-run-auto-save-hook!)
  ((force %safe-run-hooks!) 'auto-save-hook))

;;; --- M47 imp-2: the 26 typed C leaves (src/fileio.c) ----------------

(defelisp %--fileio-find-file-name-handler    --fileio-find-file-name-handler)
(defelisp %--fileio-file-name-directory       --fileio-file-name-directory)
(defelisp %--fileio-file-name-nondirectory    --fileio-file-name-nondirectory)
(defelisp %--fileio-file-name-as-directory    --fileio-file-name-as-directory)
(defelisp %--fileio-directory-file-name       --fileio-directory-file-name)
(defelisp %--fileio-file-name-concat          --fileio-file-name-concat)
(defelisp %--fileio-expand-file-name          --fileio-expand-file-name)
(defelisp %--fileio-substitute-in-file-name   --fileio-substitute-in-file-name)
(defelisp %--fileio-file-exists-p             --fileio-file-exists-p)
(defelisp %--fileio-file-executable-p         --fileio-file-executable-p)
(defelisp %--fileio-file-readable-p           --fileio-file-readable-p)
(defelisp %--fileio-file-writable-p           --fileio-file-writable-p)
(defelisp %--fileio-access-file               --fileio-access-file)
(defelisp %--fileio-file-symlink-p            --fileio-file-symlink-p)
(defelisp %--fileio-file-directory-p          --fileio-file-directory-p)
(defelisp %--fileio-file-regular-p            --fileio-file-regular-p)
(defelisp %--fileio-file-modes                --fileio-file-modes)
(defelisp %--fileio-file-newer-than-file-p    --fileio-file-newer-than-file-p)
(defelisp %--fileio-file-system-info          --fileio-file-system-info)
(defelisp %--fileio-copy-file                 --fileio-copy-file)
(defelisp %--fileio-make-directory-internal   --fileio-make-directory-internal)
(defelisp %--fileio-delete-directory-internal --fileio-delete-directory-internal)
(defelisp %--fileio-delete-file-internal      --fileio-delete-file-internal)
(defelisp %--fileio-rename-file               --fileio-rename-file)
(defelisp %--fileio-add-name-to-file          --fileio-add-name-to-file)
(defelisp %--fileio-make-symbolic-link        --fileio-make-symbolic-link)

;; G1 -- the file-name / path policy.  Each wrapper returns a plain
;; string or nil.
(define (fileio-find-file-name-handler file operation)
  ((force %--fileio-find-file-name-handler) file operation))
(define (fileio-file-name-directory fn)
  ((force %--fileio-file-name-directory) fn))
(define (fileio-file-name-nondirectory fn)
  ((force %--fileio-file-name-nondirectory) fn))
(define (fileio-file-name-as-directory fn)
  ((force %--fileio-file-name-as-directory) fn))
(define (fileio-directory-file-name fn)
  ((force %--fileio-directory-file-name) fn))
;; The C leaf is MANY-arity, so forward all the arguments.
(define (fileio-file-name-concat . args)
  (apply (force %--fileio-file-name-concat) args))
(define (fileio-expand-file-name name . rest)
  (apply (force %--fileio-expand-file-name) name rest))
(define (fileio-substitute-in-file-name fn)
  ((force %--fileio-substitute-in-file-name) fn))

;; G2 -- the OS-query predicate policy.  Each wrapper returns a plain
;; boolean, a string, an integer, a list, or nil.
(define (fileio-file-exists-p fn)
  ((force %--fileio-file-exists-p) fn))
(define (fileio-file-executable-p fn)
  ((force %--fileio-file-executable-p) fn))
(define (fileio-file-readable-p fn)
  ((force %--fileio-file-readable-p) fn))
(define (fileio-file-writable-p fn)
  ((force %--fileio-file-writable-p) fn))
(define (fileio-access-file fn op)
  ((force %--fileio-access-file) fn op))
(define (fileio-file-symlink-p fn)
  ((force %--fileio-file-symlink-p) fn))
(define (fileio-file-directory-p fn)
  ((force %--fileio-file-directory-p) fn))
(define (fileio-file-regular-p fn)
  ((force %--fileio-file-regular-p) fn))
(define (fileio-file-modes fn)
  ((force %--fileio-file-modes) fn))
(define (fileio-file-newer-than-file-p a b)
  ((force %--fileio-file-newer-than-file-p) a b))
(define (fileio-file-system-info fn)
  ((force %--fileio-file-system-info) fn))

;; G3 -- the copy / rename / link / delete policy.  Each wrapper returns
;; a plain boolean; the leaf does NOT report a file error.
(define (fileio-copy-file file newname ok-if-exists keep-time
                          preserve-uid-gid preserve-perms)
  ((force %--fileio-copy-file) file newname ok-if-exists keep-time
   preserve-uid-gid preserve-perms))
(define (fileio-make-directory-internal dir)
  ((force %--fileio-make-directory-internal) dir))
(define (fileio-delete-directory-internal dir)
  ((force %--fileio-delete-directory-internal) dir))
(define (fileio-delete-file-internal fn)
  ((force %--fileio-delete-file-internal) fn))
(define (fileio-rename-file file newname ok-if-exists)
  ((force %--fileio-rename-file) file newname ok-if-exists))
(define (fileio-add-name-to-file file newname ok-if-exists)
  ((force %--fileio-add-name-to-file) file newname ok-if-exists))
(define (fileio-make-symbolic-link target linkname ok-if-exists)
  ((force %--fileio-make-symbolic-link) target linkname ok-if-exists))
