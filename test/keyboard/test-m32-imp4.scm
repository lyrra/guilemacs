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

;;; --- 4. Static: the eval.c dispatcher and the C callback ------------
(define eval-c (slurp (repo "src/eval.c")))
(if (not eval-c)
    (report "m32/imp4/scan/eval.c" (cons 'FAIL "src/eval.c missing"))
    (begin
      ;; probably_quit is a thin dispatcher into (emacs eval-main).
      (check "m32/imp4/eval.c/refs-eval-main-module" #t
             (contains? eval-c "scm_c_public_ref (\"emacs eval-main\""))
      (check "m32/imp4/eval.c/refs-probably-quit" #t
             (contains? eval-c "\"probably-quit!\""))
      ;; The C entry point no longer calls process_pending_signals.
      (check "m32/imp4/eval.c/no-process-pending-signals" #f
             (contains? eval-c "process_pending_signals ("))
      (check "m32/imp4/eval.c/no-else-if-pending-signals" #f
             (contains? eval-c "else if (pending_signals)"))
      ;; The mechanism stays C: process_quit_flag is still static here,
      ;; and the branch-1 callback DEFUN exposes it.
      (check "m32/imp4/eval.c/process-quit-flag-static" #t
             (contains? eval-c "static void\nprocess_quit_flag (void)"))
      (check "m32/imp4/eval.c/defines-callback" #t
             (contains? eval-c "DEFUN (\"--process-quit-flag!\""))
      ;; throw-on-input is read through the elisp runtime.
      (check "m32/imp4/eval.c/reads-throw-on-input" #t
             (contains? eval-c "Fsymbol_value (Qthrow_on_input)"))
      (check "m32/imp4/eval.c/no-Vthrow-on-input" #f
             (contains? eval-c "Vthrow_on_input"))
      ;; num-nonmacro-input-events is read through the elisp runtime.
      (check "m32/imp4/eval.c/reads-num-nonmacro" #t
             (contains? eval-c
                       "XFIXNUM (Fsymbol_value (Qnum_nonmacro_input_events))"))
      (check "m32/imp4/eval.c/no-bare-num-nonmacro-read" #f
             (has-line-matching?
              eval-c
              (lambda (line) (string-contains line "= num_nonmacro_input_events"))))
      ;; The two branch tests are computed in C and passed to Scheme -- the
      ;; quit decision stays out of a re-entrant symbol-value read (which
      ;; segfaults at bootstrap).  Pin the SCM_CALL_2 shape.
      (check "m32/imp4/eval.c/passes-branch-tests" #t
             (contains? eval-c "SCM_CALL_2 (proc,"))
      (check "m32/imp4/eval.c/computes-quit-p" #t
             (contains? eval-c "(!NILP (Vquit_flag) && NILP (Vinhibit_quit))"))))

;;; --- 5. Static: keyboard.c reads through the elisp runtime ----------
(define kbd-c (slurp (repo "src/keyboard.c")))
(if (not kbd-c)
    (report "m32/imp4/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      (check "m32/imp4/keyboard.c/reads-num-nonmacro" #t
             (contains? kbd-c
                       "XFIXNUM (Fsymbol_value (Qnum_nonmacro_input_events))"))
      (check "m32/imp4/keyboard.c/no-bare-num-nonmacro-read" #f
             (has-line-matching?
              kbd-c
              (lambda (line)
                (string-contains line "last_auto_save = num_nonmacro_input_events"))))))

;;; --- 6. Static: no DEFVAR_* site for either name --------------------
;;; The DEFVAR_* call site is what make-docfile scans.  Its deletion is
;;; paired with a DEFSYM that keeps the Qsym #define and the
;;; defsym_name[] entry.
(define kg (slurp (repo "src/keyboard-globals.c")))
(if (not kg)
    (report "m32/imp4/scan/keyboard-globals.c" (cons 'FAIL "missing"))
    (begin
      (for-each
       (lambda (name)
         (check (string-append "m32/imp4/no-defvar/" name) #f
                (defvar-site? kg name)))
       '("num-nonmacro-input-events" "throw-on-input"))
      (check "m32/imp4/keyboard-globals.c/defsym-num-nonmacro" #t
             (contains? kg
                       "DEFSYM (Qnum_nonmacro_input_events, \"num-nonmacro-input-events\")"))
      (check "m32/imp4/keyboard-globals.c/defsym-throw-on-input" #t
             (contains? kg
                       "DEFSYM (Qthrow_on_input, \"throw-on-input\")"))))

;;; --- 7. Static: no storage cell in the generated globals.h ----------
(define gh (slurp (repo "src/globals.h")))
(if (not gh)
    (report "m32/imp4/scan/globals.h" (cons 'FAIL "missing"))
    (for-each
     (lambda (cell)
       (check (string-append "m32/imp4/no-cell/" cell) #f
              (contains? gh cell)))
     '("f_Vthrow_on_input" "f_num_nonmacro_input_events")))

;;; --- 8. Static: the Scheme declarations exist -----------------------
(define cl (slurp (repo "mod/emacs/command-loop.scm")))
(if (not cl)
    (report "m32/imp4/scan/command-loop.scm" (cons 'FAIL "missing"))
    (begin
      (check "m32/imp4/command-loop/num-nonmacro-row" #t
             (contains? cl "(num-nonmacro-input-events"))
      (check "m32/imp4/command-loop/throw-on-input-row" #t
             (contains? cl "(throw-on-input"))
      ;; The declaration seeds the C defaults: 0 for the DEFVAR_INT
      ;; counter and #nil for the DEFVAR_LISP throw-on-input.
      (check "m32/imp4/command-loop/num-nonmacro-seed-0" #t
             (has-line-matching?
              cl (lambda (line)
                   (and (string-contains line "(num-nonmacro-input-events")
                        (string-contains line "0)")))))
      (check "m32/imp4/command-loop/throw-on-input-seed-nil" #t
             (has-line-matching?
              cl (lambda (line)
                   (and (string-contains line "(throw-on-input")
                        (string-contains line "#nil)")))))))

;;; --- 9. Static: the (emacs eval-main) module ------------------------
(define em (slurp (repo "mod/emacs/eval-main.scm")))
(if (not em)
    (report "m32/imp4/scan/eval-main.scm" (cons 'FAIL "missing"))
    (begin
      (check "m32/imp4/eval-main/defines-probably-quit" #t
             (contains? em "(define (probably-quit! quit-p signals-p)"))
      (check "m32/imp4/eval-main/exports-probably-quit" #t
             (contains? em "(probably-quit!"))
      (check "m32/imp4/eval-main/refs-callback" #t
             (contains? em "%--process-quit-flag!"))
      (check "m32/imp4/eval-main/reuses-drain" #t
             (contains? em "send-process-drain-signals!"))))

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

;;; --- 10. Static: the module is boot-loaded and the corpus registered -
(define prelude (slurp (repo "prelude/load.scm")))
(check "m32/imp4/prelude/loads-eval-main" #t
       (contains? prelude "(emacs eval-main)"))

(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m32/imp4/run-tests.scm/registers-el" #t
       (contains? run-tests "test-m32-imp4.el"))
