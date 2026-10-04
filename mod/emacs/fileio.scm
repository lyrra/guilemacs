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

;;; --- G1: the file-name / path policy (M47 imp-3) --------------------
;;;
;;; Reading B (brief.org section 4 / section 5): the module owns the
;;; path *decision*; the C leaf holds the byte-level *mechanism*.  Most
;;; procedures below call the Scheme path procedure of
;;; (emacs lookup-functions) first, and call their C leaf only when the
;;; Scheme procedure yields no value.  The expand-file-name and
;;; substitute-in-file-name decisions are module-local Scheme, because
;;; no path procedure for them exists (cr.org F2).  The leaf never
;;; recurses into its own hub (cr.org F1).

;; Resolve the reused path procedures of (emacs lookup-functions)
;; lazily, so this module does not eagerly import it (the M9-M46
;; convention, cf. the %safe-run-hooks! delay above).
(define %file-path-directory
  (delay (module-ref (resolve-module '(emacs lookup-functions))
                     'file-path-directory)))
(define %file-path-nondirectory
  (delay (module-ref (resolve-module '(emacs lookup-functions))
                     'file-path-nondirectory)))
(define %ends-with-directory-separator?
  (delay (module-ref (resolve-module '(emacs lookup-functions))
                     'ends-with-directory-separator?)))

;; The alist walk is pure C; the module passes through to the leaf.
;; (The handler *dispatch* stays in the C hub.)
(define (fileio-find-file-name-handler file operation)
  ((force %--fileio-find-file-name-handler) file operation))

;; The directory is the file-path-directory decision.  An empty result
;; means "no directory", so fall back to the C mechanism (nil).
(define (fileio-file-name-directory fn)
  (if (string? fn)
      (let ((dir ((force %file-path-directory) fn)))
        (if (and (string? dir) (> (string-length dir) 0))
            dir
            ((force %--fileio-file-name-directory) fn)))
      ((force %--fileio-file-name-directory) fn)))

;; The non-directory decision is the file-path-nondirectory split.  When
;; the Scheme split yields no value, the C mechanism `file_name_
;; nondirectory_1' runs (cr.org F6).
(define (fileio-file-name-nondirectory fn)
  (if (string? fn)
      (let ((nd ((force %file-path-nondirectory) fn)))
        (if (string? nd) nd ((force %--fileio-file-name-nondirectory) fn)))
      ((force %--fileio-file-name-nondirectory) fn)))

;; A name that already ends with a directory separator is a directory
;; name; otherwise the C mechanism appends the separator.
(define (fileio-file-name-as-directory fn)
  (if (and (string? fn) ((force %ends-with-directory-separator?) fn))
      fn
      ((force %--fileio-file-name-as-directory) fn)))

;; Strip the final separators in Scheme; keep "/" and "//" alone.
(define (fileio--directory-name-strip fn)
  (if (string=? fn "//")
      fn
      (let loop ((i (string-length fn)))
        (if (and (> i 1) (char=? (string-ref fn (- i 1)) #\/))
            (loop (- i 1))
            (substring fn 0 i)))))

(define (fileio-directory-file-name fn)
  (if (string? fn)
      (fileio--directory-name-strip fn)
      ((force %--fileio-directory-file-name) fn)))

;; The join decision: drop nil / empty components and insert a
;; separator between components.  A bad type falls back to the C leaf
;; (which returns nil).
(define (fileio--concat-ok? args)
  (cond ((null? args) #t)
        ((or (string? (car args)) (not (car args)))
         (fileio--concat-ok? (cdr args)))
        (else #f)))

(define (fileio-file-name-concat . args)
  (if (fileio--concat-ok? args)
      (let loop ((rest args) (acc #f))
        (cond
         ((null? rest) (or acc ""))
         ((or (not (car rest))
              (and (string? (car rest)) (= 0 (string-length (car rest)))))
          (loop (cdr rest) acc))
         (else
          (loop (cdr rest)
                (if acc
                    (string-append acc
                                   (if ((force %ends-with-directory-separator?)
                                        acc)
                                       "" "/")
                                   (car rest))
                    (car rest))))))
      (apply (force %--fileio-file-name-concat) args)))

;; The two G1 blocks whose C policy was interleaved with the handler
;; dispatch.  The C leaf now holds the byte-level mechanism; the module
;; owns the decision (cr.org F2).  Each procedure returns its input
;; unchanged when the path holds no work for the byte scan, and calls
;; its C leaf only when the Scheme decision yields no value
;; (brief.org section 5.2, Reading B).

(define (fileio--has-substring? s sub)
  "Non-nil when S holds SUB as a substring."
  (let ((n (string-length s)) (m (string-length sub)))
    (let loop ((i 0))
      (cond ((> (+ i m) n) #f)
            ((string=? (substring s i (+ i m)) sub) #t)
            (else (loop (+ i 1)))))))

(define (fileio--ends-with? s suffix)
  "Non-nil when S ends with SUFFIX."
  (let ((n (string-length s)) (m (string-length suffix)))
    (and (>= n m) (string=? (substring s (- n m) n) suffix))))

;; The default-directory decision.  An absolute path that holds no
;; `.` / `..` component and no doubled separator expands to itself, so
;; the module answers without the byte scan; all other names fall
;; through to the leaf.
(define (fileio--expand-decision name)
  (and (string? name)
       (> (string-length name) 0)
       (char=? (string-ref name 0) #\/)
       (not (fileio--has-substring? name "//"))
       (not (fileio--has-substring? name "/./"))
       (not (fileio--has-substring? name "/../"))
       (not (fileio--ends-with? name "/."))
       (not (fileio--ends-with? name "/.."))
       name))

(define (fileio-expand-file-name name . rest)
  (if (fileio--expand-decision name)
      name
      (apply (force %--fileio-expand-file-name) name rest)))

;; The substitution decision.  A name with no `$', `~', or doubled
;; separator work is returned unchanged; the leaf runs otherwise.
(define (fileio--needs-substitution? fn)
  (or (fileio--has-substring? fn "$")
      (fileio--has-substring? fn "~")
      (let ((n (string-length fn)))
        (let loop ((i 1))
          (cond ((>= i n) #f)
                ((and (char=? (string-ref fn i) #\/)
                      (char=? (string-ref fn (- i 1)) #\/)) #t)
                (else (loop (+ i 1))))))))

(define (fileio-substitute-in-file-name fn)
  (if (and (string? fn) (not (fileio--needs-substitution? fn)))
      fn
      ((force %--fileio-substitute-in-file-name) fn)))

;; G2 -- the OS-query predicate policy (M47 imp-4).  The C leaf holds the
;; OS query; this module holds the decision (brief.org section 6).  Each
;; procedure calls its leaf through the delay and returns a plain Scheme
;; value: #t / #f, a string, an integer, a list, or #f.  The module makes
;; no FFI call and no raw syscall.
(define (fileio-file-exists-p fn)
  (let ((r ((force %--fileio-file-exists-p) fn)))
    (if r #t #f)))
(define (fileio-file-executable-p fn)
  (let ((r ((force %--fileio-file-executable-p) fn)))
    (if r #t #f)))
(define (fileio-file-readable-p fn)
  (let ((r ((force %--fileio-file-readable-p) fn)))
    (if r #t #f)))
(define (fileio-file-writable-p fn)
  (let ((r ((force %--fileio-file-writable-p) fn)))
    (if r #t #f)))
(define (fileio-access-file fn op)
  (let ((r ((force %--fileio-access-file) fn op)))
    (if r #t #f)))
(define (fileio-file-symlink-p fn)
  (let ((r ((force %--fileio-file-symlink-p) fn)))
    (if (string? r) r #f)))
(define (fileio-file-directory-p fn)
  (let ((r ((force %--fileio-file-directory-p) fn)))
    (if r #t #f)))
(define (fileio-file-regular-p fn)
  (let ((r ((force %--fileio-file-regular-p) fn)))
    (if r #t #f)))
(define (fileio-file-modes fn nofollow)
  (let ((r ((force %--fileio-file-modes) fn nofollow)))
    (if r r #f)))
(define (fileio-file-newer-than-file-p a b)
  (let ((r ((force %--fileio-file-newer-than-file-p) a b)))
    (if r #t #f)))
(define (fileio-file-system-info fn)
  (let ((r ((force %--fileio-file-system-info) fn)))
    (if (pair? r) r #f)))

;; G3 -- the copy / rename / link / delete policy (M47 imp-5).  The
;; module owns the target-name resolution (the expand_cp_target policy)
;; and the overwrite / preserve decision; the C leaf holds the OS
;; mechanism (brief.org section 6).  Each procedure returns a plain
;; value: a boolean, an integer `errno', or #f.  The module makes no FFI
;; call and no raw syscall.

(define (fileio--starts-with? s prefix)
  "Non-nil when S starts with PREFIX."
  (let ((n (string-length s)) (m (string-length prefix)))
    (and (>= n m) (string=? (substring s 0 m) prefix))))

;; The expand_cp_target decision: if NEWNAME is a directory name, the
;; target is the expansion of the basename of FILE under NEWNAME;
;; otherwise the target is the expansion of NEWNAME.
(define (fileio--resolve-target file newname)
  (if (and (string? newname)
           ((force %ends-with-directory-separator?) newname))
      (fileio-expand-file-name (fileio-file-name-nondirectory file) newname)
      (fileio-expand-file-name newname)))

(define (fileio-copy-file file newname ok-if-exists keep-time
                          preserve-uid-gid preserve-perms)
  (let ((target (fileio--resolve-target file newname)))
    ((force %--fileio-copy-file) file target ok-if-exists keep-time
     preserve-uid-gid preserve-perms)))

(define (fileio-make-directory-internal dir)
  (if (string? dir)
      ((force %--fileio-make-directory-internal) dir)
      #f))

;; The remove decision strips the final separator first (brief.org
;; section 6).
(define (fileio-delete-directory-internal dir)
  (if (string? dir)
      ((force %--fileio-delete-directory-internal)
       (fileio-directory-file-name dir))
      #f))

(define (fileio-delete-file-internal fn)
  (if (string? fn)
      ((force %--fileio-delete-file-internal) fn)
      #f))

;; The overwrite decision: a non-nil, non-integer OK-IF-EXISTS means a
;; plain rename; otherwise try emacs_renameat_noreplace first.
(define (fileio-rename-file file newname ok-if-exists)
  (let* ((plain (and ok-if-exists (not (integer? ok-if-exists))))
         (target (fileio--resolve-target
                  (fileio-directory-file-name file) newname)))
    ((force %--fileio-rename-file) file target (if plain #t #f))))

(define (fileio-add-name-to-file file newname ok-if-exists)
  (let ((target (fileio--resolve-target file newname)))
    ((force %--fileio-add-name-to-file) file target ok-if-exists)))

;; The ~ / /: target rule applies only when OK-IF-EXISTS is an integer
;; (brief.org section 6).  A leading "~" expands; a leading "/:" is
;; stripped.
(define (fileio--symlink-target target ok-if-exists)
  (if (not (and (string? target) (integer? ok-if-exists)))
      target
      (cond ((fileio--starts-with? target "~")
             (fileio-expand-file-name target))
            ((fileio--starts-with? target "/:")
             (substring target 2))
            (else target))))

(define (fileio-make-symbolic-link target linkname ok-if-exists)
  (let* ((target (fileio--symlink-target target ok-if-exists))
         (link (fileio--resolve-target target linkname)))
    ((force %--fileio-make-symbolic-link) target link ok-if-exists)))
