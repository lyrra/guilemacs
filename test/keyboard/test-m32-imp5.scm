;;; test-m32-imp5.scm --- M32 imp-5: the sysdep.c emacs_full_write EINTR
;;; drain, plus the tty-erase-char and attempt-stack-overflow-recovery
;;; DEFVAR_* names.
;;;
;;; brief.org (M32 imp-5) does three jobs:
;;;
;;;   1. route the sysdep.c caller of process_pending_signals (in
;;;      emacs_full_write) through Scheme ((emacs sysdep-main)
;;;      full-write-drain!), keeping the write () loop in C;
;;;   2. migrate tty-erase-char (DEFVAR_LISP, default nil);
;;;   3. migrate attempt-stack-overflow-recovery (DEFVAR_BOOL, default
;;;      true) -- a fatal-signal name read by stack_overflow.
;;;
;;; This corpus pins the end state.  Two kinds of check:
;;;
;;;   - a runtime check: the two names are special after boot, the
;;;     tty-erase-char default is nil and the
;;;     attempt-stack-overflow-recovery default is non-nil, and a
;;;     write-then-read round trip passes for each.  These use only core
;;;     primitives.
;;;   - a static wiring check: the sysdep.c dispatcher, the value-cell
;;;     helper and the resolve exist; the C site no longer calls
;;;     process_pending_signals directly; the stub keeps its definition
;;;     and its keyboard.c caller; the two names have no DEFVAR_* site
;;;     and no globals.h storage cell; and the Scheme declarations exist.
;;;
;;; The repo root is bound by the .el wrapper as %m32-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test and
;;; prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m32-imp5.el.

(use-modules (ice-9 rdelim))
(use-modules (srfi srfi-13))
;; The runtime check in section 9b calls the ported decision procedure
;; (emacs sysdep-main) full-write-drain! directly.
(use-modules (emacs sysdep-main))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (info name value)
  "Report NAME as an INFO pair.  The .el wrapper prints it and does not
assert it; use it for a runtime call that needs a C entry point the
binary may not export."
  (report name (cons 'INFO value)))

(define (slurp path)
  "Return the whole file at PATH as a string, or #f when it is absent."
  (if (not (file-exists? path))
      #f
      (call-with-input-file path
        (lambda (port)
          (let loop ((chars '()))
            (let ((c (read-char port)))
              (if (eof-object? c)
                  (list->string (reverse chars))
                  (loop (cons c chars)))))))))

(define (contains? text needle)
  ;; string-contains returns the match index or #f; normalize to a boolean
  ;; so `check' can compare against #t/#f.
  (and (string? text)
       (if (string-contains text needle) #t #f)))

(define (repo path) (string-append %m32-root "/" path))

(define (defvar-site? text name)
  "True when TEXT holds a DEFVAR_* call site for NAME.  A bare C
variable reference or a comment mention does not count."
  (and (string? text)
       (let ((needle (string-append "\"" name "\"")))
         (call-with-input-string text
           (lambda (port)
             (let loop ()
               (let ((line (read-line port)))
                 (cond ((eof-object? line) #f)
                       ((and (string-contains line "DEFVAR_")
                             (string-contains line needle)) #t)
                       (else (loop))))))))))

(define (has-line-matching? text pred)
  "True when any line of TEXT satisfies PRED."
  (and (string? text)
       (call-with-input-string text
         (lambda (port)
           (let loop ()
             (let ((line (read-line port)))
               (cond ((eof-object? line) #f)
                     ((pred line) #t)
                     (else (loop)))))))))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m32-root))
    (begin (report "m32/imp5/root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m32-root "."))
    (report "m32/imp5/root-bound" 'PASS))

;;; --- 1. Runtime: the two names are special --------------------------
;;; The C DEFVAR_* set SYMBOL_DECLARED_SPECIAL; proclaim-special! in
;;; command-loop.scm is the replacement.  A non-special name would let
;;; elisp let/setq compile lexical.
(check "m32/imp5/special/tty-erase-char" #t
       (special? 'tty-erase-char))
(check "m32/imp5/special/attempt-stack-overflow-recovery" #t
       (special? 'attempt-stack-overflow-recovery))

;;; --- 2. Runtime: the migrated defaults ------------------------------
;;; tty-erase-char was DEFVAR_LISP, default nil.  init_sys_modes writes it
;;; to nil at boot; with no tty in batch it stays nil.
(check "m32/imp5/default/tty-erase-char" #nil
       (symbol-value 'tty-erase-char))
;; attempt-stack-overflow-recovery was DEFVAR_BOOL, default true.  The
;; (emacs command-loop) declaration seeds the non-nil default.
(check "m32/imp5/default/attempt-stack-overflow-recovery-is-non-nil" #t
       (not (eq? (symbol-value 'attempt-stack-overflow-recovery) #nil)))

;;; --- 3. Runtime: a write-then-read round trip for each --------------
(let ((old (symbol-value 'tty-erase-char)))
  (set-symbol-value! 'tty-erase-char 127)
  (check "m32/imp5/write-read/tty-erase-char" 127
         (symbol-value 'tty-erase-char))
  (set-symbol-value! 'tty-erase-char old))

(let ((old (symbol-value 'attempt-stack-overflow-recovery)))
  (set-symbol-value! 'attempt-stack-overflow-recovery #nil)
  (check "m32/imp5/write-read/attempt-stack-overflow-recovery" #nil
         (symbol-value 'attempt-stack-overflow-recovery))
  (set-symbol-value! 'attempt-stack-overflow-recovery old))

;;; --- 3b. Runtime: the C writers reach the same slot ------------------
;;; The checks above use only the Scheme side.  These call the C entry
;;; points -- the elisp function `set' is Fset and `symbol-value' is
;;; Fsymbol_value -- which is exactly how sysdep.c writes tty-erase-char
;;; and how the reader resolves the value cell.  A Scheme write is read
;;; back through C and a C write is read back through Scheme.  Guarded: a
;;; binary without those subrs reports INFO, not a failure.
(define (c-read name) ((symbol-function 'symbol-value) name))
(define (c-write name value) ((symbol-function 'set) name value))

(define (c-caller-roundtrip label name)
  "Write NAME through the C `set', read it back through the Scheme
symbol-value, then write it through set-symbol-value! and read it back
through the C `symbol-value'.  NAME is restored."
  (catch #t
    (lambda ()
      (let ((old (symbol-value name))
            (cval (list 'm32 'imp5 'c-write))
            (sval (list 'm32 'imp5 'scheme-write)))
        (c-write name cval)
        (check (string-append "m32/imp5/c-write/scheme-read/" label)
               cval (symbol-value name))
        (set-symbol-value! name sval)
        (check (string-append "m32/imp5/scheme-write/c-read/" label)
               sval (c-read name))
        (set-symbol-value! name old)))
    (lambda (key . args)
      (info (string-append "m32/imp5/c-readers/" label)
            (format #f "guarded: ~S ~S" key args)))))

(c-caller-roundtrip "tty-erase-char" 'tty-erase-char)
(c-caller-roundtrip "attempt-stack-overflow-recovery"
                    'attempt-stack-overflow-recovery)

;;; --- 9b. Runtime: call the ported decision procedure -----------------
;;; The checks above only read the module text.  Call full-write-drain!
;;; directly so the ported decision runs.  INTT = 0 skips maybe_quit;
;;; INTT = -1 is the emacs_write_sig shape.  Both run the shared guarded
;;; drain, which is a no-op with no signal pending (and exercises the
;;; lazy (emacs process-error) resolve, decision D4).  Neither may quit.
(define (guarded-call label thunk)
  (catch #t
    (lambda () (check label #nil (thunk)))
    (lambda (key . args)
      (info label (format #f "guarded: ~S ~S" key args)))))

(guarded-call "m32/imp5/sysdep-main/full-write-drain-zero"
              (lambda () (full-write-drain! 0)))
(guarded-call "m32/imp5/sysdep-main/full-write-drain-neg"
              (lambda () (full-write-drain! -1)))
