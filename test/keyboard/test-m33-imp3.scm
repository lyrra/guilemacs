;;; test-m33-imp3.scm --- M33 imp-3: the xterm.c help-event decision.
;;;
;;; brief.org (M33 imp-3) moves the help-event decision of
;;; handle_one_xevent in src/xterm.c into the new module (emacs xterm),
;;; procedure x-help-event-action.  The C mechanism stays C.  See
;;; docs/m33-plan.org A2 ... A3.
;;;
;;; This corpus pins the port end state.  Two kinds of check:
;;;
;;;   - a runtime check: the module loads and exports the procedure,
;;;     and the four decision cases return the documented fixnums.
;;;     The procedure is pure Scheme, so no rebuilt binary is needed.
;;;   - a static wiring check: src/xterm.c holds the dispatcher and the
;;;     module reference; src/xterm.c includes guile.h; the gen_help_event
;;;     stub stays in src/keyboard.c and src/keyboard.h; the module is
;;;     boot-loaded.
;;;
;;; The repo root is bound by the .el wrapper as %m33-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test
;;; and prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m33-imp3.el.

(use-modules (ice-9 rdelim))
(use-modules (srfi srfi-13))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

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

(define (repo path) (string-append %m33-root "/" path))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m33-root))
    (begin (report "m33-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m33-root "."))
    (report "m33-root-bound" 'PASS))

;;; --- 1. The module loads and exports the procedure ----------------
(use-modules (emacs xterm))

(define (exported? name)
  (let ((p (module-ref (resolve-module '(emacs xterm)) name)))
    (procedure? p)))

(check "m33/imp3/export/x-help-event-action" #t
       (exported? 'x-help-event-action))

;;; --- 2. Runtime: the four decision cases ---------------------------
;;; The procedure is pure Scheme.  Assert every case from brief.org 7.1.
(check "m33/imp3/runtime/no-help" 0
       (x-help-event-action 0 #f))
(check "m33/imp3/runtime/show-help" 1
       (x-help-event-action 1 #f))
(check "m33/imp3/runtime/hold-quit-overrides" 0
       (x-help-event-action 1 #t))
(check "m33/imp3/runtime/clear-help" 2
       (x-help-event-action -1 #f))
;; Extra pin: a positive DO-HELP with a held quit event still skips.
(check "m33/imp3/runtime/positive-hold-quit" 0
       (x-help-event-action 3 #t))

;;; --- 3. Static: src/xterm.c holds the dispatcher and the include ---
(define xterm-c (slurp (repo "src/xterm.c")))
(if (not xterm-c)
    (report "m33/imp3/scan/xterm.c" (cons 'FAIL "src/xterm.c missing"))
    (begin
      (check "m33/imp3/xterm.c/includes-guile.h" #t
             (contains? xterm-c "#include \"guile.h\""))
      (check "m33/imp3/xterm.c/defines-dispatcher" #t
             (contains? xterm-c "x_help_event_action (int do_help, bool hold_quit_p)"))
      (check "m33/imp3/xterm.c/dispatches-module" #t
             (contains? xterm-c "\"emacs xterm\", \"x-help-event-action\""))
      ;; The call site computes the guard value in C and passes it.
      (check "m33/imp3/xterm.c/calls-dispatcher" #t
             (contains? xterm-c "x_help_event_action (do_help,"))
      (check "m33/imp3/xterm.c/guard-in-c" #t
             (contains? xterm-c "hold_quit && hold_quit->kind != NO_EVENT"))
      ;; The gen_help_event stub stays (its retirement waits for M34).
      (check "m33/imp3/xterm.c/still-calls-gen-help-event" #t
             (contains? xterm-c "gen_help_event (help_echo_string, frame,"))
      (check "m33/imp3/xterm.c/still-clears-and-calls-gen-help-event" #t
             (contains? xterm-c "gen_help_event (Qnil, frame, Qnil, Qnil, 0)"))
      ;; The old branch head is gone.
      (check "m33/imp3/xterm.c/no-old-do-help-branch" #f
             (contains? xterm-c "if (do_help > 0)"))
      ;; The XInput2 mechanism stays C.
      (check "m33/imp3/xterm.c/keeps-xi-interaction" #t
             (contains? xterm-c "xi_handle_interaction (dpyinfo, f,"))
      ;; The XSETFRAME conversion stays C.
      (check "m33/imp3/xterm.c/keeps-xsetframe" #t
             (contains? xterm-c "XSETFRAME (frame, f)"))))

;;; --- 4. Static: src/keyboard.c still defines gen_help_event --------
(define kbd-c (slurp (repo "src/keyboard.c")))
(if (not kbd-c)
    (report "m33/imp3/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (check "m33/imp3/keyboard.c/still-defines-gen-help-event" #t
           (contains? kbd-c "gen_help_event (Lisp_Object help, Lisp_Object frame")))

;;; --- 5. Static: src/keyboard.h still declares gen_help_event -------
(define kbd-h (slurp (repo "src/keyboard.h")))
(if (not kbd-h)
    (report "m33/imp3/scan/keyboard.h" (cons 'FAIL "src/keyboard.h missing"))
    (check "m33/imp3/keyboard.h/still-declares-gen-help-event" #t
           (contains? kbd-h "extern void gen_help_event (Lisp_Object, Lisp_Object, Lisp_Object,")))

;;; --- 6. Static: the module source shapes the decision arms ---------
(define xterm-mod (slurp (repo "mod/emacs/xterm.scm")))
(if (not xterm-mod)
    (report "m33/imp3/scan/module" (cons 'FAIL "mod/emacs/xterm.scm missing"))
    (begin
      (check "m33/imp3/module/declarative" #t
             (contains? xterm-mod "#:declarative? #t"))
      (check "m33/imp3/module/exports-procedure" #t
             (contains? xterm-mod "x-help-event-action"))
      ;; The three-way choice must be present in this order:
      ;; zero -> 0, hold-quit -> 0, positive -> 1, else -> 2.
      (check "m33/imp3/module/three-way-choice" #t
             (and (contains? xterm-mod "((= do-help 0) 0)")
                  (contains? xterm-mod "(hold-quit-p 0)")
                  (contains? xterm-mod "((> do-help 0) 1)")
                  (contains? xterm-mod "(else 2)")))))

;;; --- 7. Static: boot load ------------------------------------------
(define load-scm (slurp (repo "prelude/load.scm")))
(if (not load-scm)
    (report "m33/imp3/scan/load.scm" (cons 'FAIL "prelude/load.scm missing"))
    (check "m33/imp3/load.scm/registers-module" #t
           (contains? load-scm "(emacs xterm)")))

(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m33/imp3/run-tests.scm/registers-el" #t
       (contains? run-tests "test-m33-imp3.el"))
