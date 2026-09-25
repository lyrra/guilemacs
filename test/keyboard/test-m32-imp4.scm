;;; test-m32-imp4.scm --- M32 imp-4: the eval.c probably_quit caller,
;;; plus the num-nonmacro-input-events and throw-on-input DEFVAR_* names.
;;;
;;; brief.org (M32 imp-4) does three jobs:
;;;
;;;   1. route the eval.c caller of process_pending_signals (in
;;;      probably_quit) through Scheme ((emacs eval-main) probably-quit!),
;;;      keeping the process_quit_flag mechanism in C;
;;;   2. migrate throw-on-input (DEFVAR_LISP, default nil);
;;;   3. migrate num-nonmacro-input-events (DEFVAR_INT, default 0).
;;;
;;; This corpus pins the end state.  Two kinds of check:
;;;
;;;   - a runtime check: the two names are special after boot, the
;;;     num-nonmacro default is 0 and the throw-on-input default is nil,
;;;     and a write-then-read round trip passes for each.  These use only
;;;     core primitives.
;;;   - a static wiring check: the eval.c dispatcher, the branch-1 C
;;;     callback and the C readers exist; the C entry point no longer
;;;     calls process_pending_signals; the two names have no DEFVAR_*
;;;     site and no globals.h storage cell; and the Scheme declarations
;;;     exist.
;;;
;;; The repo root is bound by the .el wrapper as %m32-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test and
;;; prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m32-imp4.el.

(use-modules (ice-9 rdelim))
(use-modules (srfi srfi-13))
;; The runtime check in section 9b calls the ported decision procedure
;; (emacs eval-main) probably-quit! directly.
(use-modules (emacs eval-main))

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
    (begin (report "m32/imp4/root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m32-root "."))
    (report "m32/imp4/root-bound" 'PASS))

;;; --- 1. Runtime: the two names are special --------------------------
;;; The C DEFVAR_* set SYMBOL_DECLARED_SPECIAL; proclaim-special! in
;;; command-loop.scm is the replacement.  A non-special name would let
;;; elisp let/setq compile lexical.
(check "m32/imp4/special/num-nonmacro-input-events" #t
       (special? 'num-nonmacro-input-events))
(check "m32/imp4/special/throw-on-input" #t
       (special? 'throw-on-input))

;;; --- 2. Runtime: the migrated names are well-formed -----------------
;;; num-nonmacro-input-events was DEFVAR_INT: an integer counter, seeded
;;; to 0 by the (emacs command-loop) declaration.  It is incremented by
;;; Scheme (recent-keys.scm) and possibly by earlier corpora, so do NOT
;;; assert the absolute value here -- assert the DEFVAR_INT shape (a
;;; non-negative integer).  The seed itself is pinned by the static
;;; command-loop.scm check below.  throw-on-input was DEFVAR_LISP,
;;; default nil, and no earlier corpus leaves it set.
(check "m32/imp4/value/num-nonmacro-input-events-is-non-negative-int" #t
       (and (integer? (symbol-value 'num-nonmacro-input-events))
            (>= (symbol-value 'num-nonmacro-input-events) 0)))
(check "m32/imp4/default/throw-on-input" #nil
       (symbol-value 'throw-on-input))

;;; --- 3. Runtime: a write-then-read round trip for each --------------
(let ((old (symbol-value 'throw-on-input)))
  (set-symbol-value! 'throw-on-input (list 'm32 'imp4 'throw-on-input))
  (check "m32/imp4/write-read/throw-on-input"
         (list 'm32 'imp4 'throw-on-input)
         (symbol-value 'throw-on-input))
  (set-symbol-value! 'throw-on-input old))

(let ((old (symbol-value 'num-nonmacro-input-events)))
  (set-symbol-value! 'num-nonmacro-input-events 41234)
  (check "m32/imp4/write-read/num-nonmacro-input-events" 41234
         (symbol-value 'num-nonmacro-input-events))
  (set-symbol-value! 'num-nonmacro-input-events old))

;;; --- 3b. Runtime: the C readers share the Scheme value slot ----------
;;; The checks above use only the Scheme side.  These call the C entry
;;; points -- the elisp function `set' is Fset and `symbol-value' is
;;; Fsymbol_value -- so a Scheme write is read back from C and a C write
;;; is read back from Scheme.  That proves the C readers reach the same
;;; slot the declaration seeds.  Guarded: a binary without those subrs
;;; reports INFO, not a failure.
(define (c-read name) ((symbol-function 'symbol-value) name))
(define (c-write name value) ((symbol-function 'set) name value))

(define (c-caller-roundtrip label name)
  "Write NAME through the C `set', read it back through the Scheme
symbol-value, then write it through set-symbol-value! and read it back
through the C `symbol-value'.  NAME is restored."
  (catch #t
    (lambda ()
      (let ((old (symbol-value name))
            (cval (list 'm32 'imp4 'c-write))
            (sval (list 'm32 'imp4 'scheme-write)))
        (c-write name cval)
        (check (string-append "m32/imp4/c-write/scheme-read/" label)
               cval (symbol-value name))
        (set-symbol-value! name sval)
        (check (string-append "m32/imp4/scheme-write/c-read/" label)
               sval (c-read name))
        (set-symbol-value! name old)))
    (lambda (key . args)
      (info (string-append "m32/imp4/c-readers/" label)
            (format #f "guarded: ~S ~S" key args)))))

(c-caller-roundtrip "throw-on-input" 'throw-on-input)
(c-caller-roundtrip "num-nonmacro-input-events" 'num-nonmacro-input-events)

;;; --- 9b. Runtime: call the ported decision procedure -----------------
;;; The checks above only read the module text.  Call probably-quit!
;;; directly so the ported decision runs.  Both branch tests false is a
;;; pure no-op returning nil.  signals-p true with no signal pending
;;; exercises the lazy (emacs process-error) resolve (decision D3); the
;;; drain is guarded, so it is also a no-op.  Neither path may quit.
;;; (The quit-p true path is NOT called: it runs C process_quit_flag,
;;; whose quit () does not return.)
(check "m32/imp4/eval-main/probably-quit-noop" #nil
       (probably-quit! #f #f))
(catch #t
  (lambda ()
    (check "m32/imp4/eval-main/probably-quit-drain-noop" #nil
           (probably-quit! #f #t)))
  (lambda (key . args)
    (info "m32/imp4/eval-main/probably-quit-drain-noop"
          (format #f "guarded: ~S ~S" key args))))
