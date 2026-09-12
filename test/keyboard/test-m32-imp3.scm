;;; test-m32-imp3.scm --- M32 imp-3: the emacs.c stuff_buffered_input
;;; caller, plus the top-level and attempt-orderly-shutdown-on-fatal-signal
;;; DEFVAR_* names.
;;;
;;; brief.org (M32 imp-3) does three jobs:
;;;
;;;   1. route the shut_down_emacs caller of stuff_buffered_input through
;;;      Scheme ((emacs kbd-buffer) stuff-buffered-input), keeping a
;;;      fatal-safe C drain in src/emacs.c;
;;;   2. retire the extern stuff_buffered_input (keyboard.c, keyboard.h);
;;;   3. move top-level (DEFVAR_LISP, default nil) and
;;;      attempt-orderly-shutdown-on-fatal-signal (DEFVAR_BOOL, default
;;;      true) out of C for a boot-loaded Scheme declaration.
;;;
;;; This corpus pins the end state.  Two kinds of check:
;;;
;;;   - a runtime check: the two names are special after boot, the
;;;     attempt-orderly default is true, and a write-then-read round trip
;;;     passes for each.  These use only core primitives, so a binary
;;;     that predates the imp-3 C changes still passes them.
;;;   - a static wiring check: the emacs.c dispatcher and drain exist,
;;;     stuff_buffered_input has no definition, caller or extern in
;;;     keyboard.c / keyboard.h, the C readers and writers go through the
;;;     elisp runtime, and neither name keeps a DEFVAR_* site or a
;;;     globals.h storage cell.
;;;
;;; The repo root is bound by the .el wrapper as %m32-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test and
;;; prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m32-imp3.el.

(use-modules (ice-9 rdelim))
(use-modules (srfi srfi-13))

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

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m32-root))
    (begin (report "m32/imp3/root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m32-root "."))
    (report "m32/imp3/root-bound" 'PASS))

;;; --- 1. Runtime: the two names are special --------------------------
;;; The C DEFVAR_* set SYMBOL_DECLARED_SPECIAL; proclaim-special! in
;;; command-loop.scm is the replacement.  A non-special name would let
;;; elisp let/setq compile lexical.
(check "m32/imp3/special/top-level" #t (special? 'top-level))
(check "m32/imp3/special/attempt-orderly-shutdown-on-fatal-signal" #t
       (special? 'attempt-orderly-shutdown-on-fatal-signal))

;;; --- 2. Runtime: the attempt-orderly C default (true) holds ---------
;;; The C default was true and no C writer exists, so the default value
;;; read at test time is true.
(check "m32/imp3/default/attempt-orderly-shutdown-on-fatal-signal" #t
       ((symbol-function 'default-value) 'attempt-orderly-shutdown-on-fatal-signal))

;;; --- 3. Runtime: a write-then-read round trip for each --------------
;;; top-level is rewritten at startup (main loads loadup.el), so assert a
;;; fresh write reads back, then restore.  The C writers now reach the
;;; name through the elisp runtime, i.e. the same slot this reads.
(let ((old (symbol-value 'top-level)))
  (set-symbol-value! 'top-level (list 'm32 'imp3 'top-level))
  (check "m32/imp3/write-read/top-level" (list 'm32 'imp3 'top-level)
         (symbol-value 'top-level))
  (set-symbol-value! 'top-level old))

(let ((old (symbol-value 'attempt-orderly-shutdown-on-fatal-signal)))
  (set-symbol-value! 'attempt-orderly-shutdown-on-fatal-signal #nil)
  (check "m32/imp3/write-read/attempt-orderly-shutdown-on-fatal-signal" #nil
         (symbol-value 'attempt-orderly-shutdown-on-fatal-signal))
  (set-symbol-value! 'attempt-orderly-shutdown-on-fatal-signal old))

;;; --- 3b. Runtime: the C readers/writers share the Scheme value slot --
;;; F3 (review): the checks above use only the Scheme side.  These call
;;; the C entry points -- the elisp function `set' is Fset and
;;; `symbol-value' is Fsymbol_value -- so a Scheme write is read back
;;; from C and a C write is read back from Scheme.  That proves the C
;;; readers and writers reach the same slot the declaration seeds.
;;; Guarded: a binary without those subrs reports INFO, not a failure.
(define (c-read name) ((symbol-function 'symbol-value) name))
(define (c-write name value) ((symbol-function 'set) name value))

(define (c-caller-roundtrip label name)
  "Write NAME through the C `set', read it back through the Scheme
symbol-value, then write it through set-symbol-value! and read it back
through the C `symbol-value'.  NAME is restored."
  (catch #t
    (lambda ()
      (let ((old (symbol-value name))
            (cval (list 'm32 'imp3 'c-write))
            (sval (list 'm32 'imp3 'scheme-write)))
        (c-write name cval)
        (check (string-append "m32/imp3/c-write/scheme-read/" label)
               cval (symbol-value name))
        (set-symbol-value! name sval)
        (check (string-append "m32/imp3/scheme-write/c-read/" label)
               sval (c-read name))
        (set-symbol-value! name old)))
    (lambda (key . args)
      (info (string-append "m32/imp3/c-readers/" label)
            (format #f "guarded: ~S ~S" key args)))))

(c-caller-roundtrip "top-level" 'top-level)
(c-caller-roundtrip "attempt-orderly-shutdown-on-fatal-signal"
                    'attempt-orderly-shutdown-on-fatal-signal)

;;; --- 4. Static: the emacs.c dispatcher and fatal-safe drain ---------
(define emacs-c (slurp (repo "src/emacs.c")))
(if (not emacs-c)
    (report "m32/imp3/scan/emacs.c" (cons 'FAIL "src/emacs.c missing"))
    (begin
      (check "m32/imp3/emacs.c/defines-drain" #t
             (contains? emacs-c "stuff_buffered_input_c (Lisp_Object stuffstring)"))
      (check "m32/imp3/emacs.c/defines-dispatch" #t
             (contains? emacs-c "stuff_buffered_input_dispatch (Lisp_Object stuffstring)"))
      (check "m32/imp3/emacs.c/calls-dispatch" #t
             (contains? emacs-c "stuff_buffered_input_dispatch (stuff);"))
      (check "m32/imp3/emacs.c/reads-fatal-flag" #t
             (contains? emacs-c "if (fatal_error_in_progress)"))
      (check "m32/imp3/emacs.c/refs-kbd-buffer-module" #t
             (contains? emacs-c "scm_c_public_ref (\"emacs kbd-buffer\""))
      (check "m32/imp3/emacs.c/refs-stuff-buffered-input" #t
             (contains? emacs-c "\"stuff-buffered-input\""))
      ;; top-level: the C writers and the native-comp reader go through
      ;; the elisp runtime, not a C cell.
      (check "m32/imp3/emacs.c/sets-top-level" #t
             (contains? emacs-c "Fset (Qtop_level"))
      (check "m32/imp3/emacs.c/reads-top-level" #t
             (contains? emacs-c "Fsymbol_value (Qtop_level)"))
      (check "m32/imp3/emacs.c/no-vtop-level" #f
             (contains? emacs-c "Vtop_level"))
      ;; F1 (review): the fatal-signal reader must not enter the Guile
      ;; runtime.  It reads the cached value cell, not find_symbol_value.
      (check "m32/imp3/emacs.c/reads-orderly-c-safely" #t
             (contains? emacs-c "orderly_shutdown_value ()"))
      (check "m32/imp3/emacs.c/resolves-orderly-cell" #t
             (contains? emacs-c "orderly_shutdown_value_cell\n    = XSYMBOL"))
      (check "m32/imp3/emacs.c/no-find-symbol-value-on-signal" #f
             (contains? emacs-c "find_symbol_value (intern_c_string"))))

;;; --- 5. Static: stuff_buffered_input is retired from keyboard -------
(define kbd-c (slurp (repo "src/keyboard.c")))
(if (not kbd-c)
    (report "m32/imp3/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      ;; The old definition, its C body and the old call are gone.  A
      ;; prose mention of the name in a comment is not a definition.
      (check "m32/imp3/keyboard.c/no-definition" #f
             (contains? kbd-c "stuff_buffered_input (Lisp_Object"))
      (check "m32/imp3/keyboard.c/no-c-body" #f
             (contains? kbd-c "stuff_buffered_input_c"))
      ;; --eval-top-level reads top-level through the elisp runtime.
      (check "m32/imp3/keyboard.c/eval-top-level-reads-scheme" #t
             (contains? kbd-c "Feval (Fsymbol_value (Qtop_level), Qt)"))
      ;; next_kbd_event / clear_event are now external for the drain.
      (check "m32/imp3/keyboard.c/next-kbd-event-external" #t
             (contains? kbd-c "next_kbd_event (union buffered_input_event *ptr)"))
      (check "m32/imp3/keyboard.c/clear-event-external" #t
             (contains? kbd-c "clear_event (struct input_event *event)"))))

(define kbd-h (slurp (repo "src/keyboard.h")))
(if (not kbd-h)
    (report "m32/imp3/scan/keyboard.h" (cons 'FAIL "src/keyboard.h missing"))
    (begin
      (check "m32/imp3/keyboard.h/no-stuff-buffered-input-extern" #f
             (contains? kbd-h "stuff_buffered_input"))
      (check "m32/imp3/keyboard.h/declares-next-kbd-event" #t
             (contains? kbd-h "next_kbd_event (union buffered_input_event *)"))
      (check "m32/imp3/keyboard.h/declares-clear-event" #t
             (contains? kbd-h "clear_event (struct input_event *)"))))

;;; --- 6. Static: no DEFVAR_* site for either name --------------------
;;; The DEFVAR_* call site is what make-docfile scans to emit the
;;; globals.h storage cell.  Delete the site and the storage goes.
(define kg (slurp (repo "src/keyboard-globals.c")))
(if (not kg)
    (report "m32/imp3/scan/keyboard-globals.c" (cons 'FAIL "missing"))
    (for-each
     (lambda (name)
       (check (string-append "m32/imp3/no-defvar/" name) #f
              (defvar-site? kg name)))
     '("top-level" "attempt-orderly-shutdown-on-fatal-signal")))

;;; --- 7. Static: no storage cell in the generated globals.h ----------
(define gh (slurp (repo "src/globals.h")))
(if (not gh)
    (report "m32/imp3/scan/globals.h" (cons 'FAIL "missing"))
    (for-each
     (lambda (cell)
       (check (string-append "m32/imp3/no-cell/" cell) #f
              (contains? gh cell)))
     '("f_Vtop_level" "f_attempt_orderly_shutdown_on_fatal_signal")))

;;; --- 8. Static: the Scheme declarations exist -----------------------
(define cl (slurp (repo "mod/emacs/command-loop.scm")))
(if (not cl)
    (report "m32/imp3/scan/command-loop.scm" (cons 'FAIL "missing"))
    (begin
      (check "m32/imp3/command-loop/top-level-row" #t
             (contains? cl "(top-level"))
      (check "m32/imp3/command-loop/attempt-orderly-row" #t
             (contains? cl "attempt-orderly-shutdown-on-fatal-signal"))))

;;; --- 9. Static: registration + the M23 imp-5 edit -------------------
(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m32/imp3/run-tests.scm/registers-el" #t
       (contains? run-tests "test-m32-imp3.el"))

(define m23 (slurp (repo "test/keyboard/test-m23-imp5.el")))
(check "m32/imp3/m23-imp5/drops-attempt-orderly" #f
       (contains? m23 "attempt-orderly-shutdown-on-fatal-signal"))
