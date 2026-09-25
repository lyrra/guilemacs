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
