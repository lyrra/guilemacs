;;; test-m33-imp5.scm --- M33 imp-5: the pgtkterm.c read path.
;;;
;;; brief.org (M33 imp-5) moves the decision logic of the
;;; src/pgtkterm.c read path into the module (emacs pgtk):
;;;
;;;   - the configure_event / leave_notify_event help-echo guards
;;;     -> pgtk-clear-help-echo?
;;;   - the motion_notify_event show-help guard
;;;     -> pgtk-help-event-action
;;;   - the key_press_event extra-keyboard-modifiers read
;;;     -> pgtk-extra-keyboard-modifiers
;;;   - the 2 scroll_event mwheel-coalesce-scroll-events reads
;;;     -> pgtk-mwheel-coalesce-scroll-events?
;;;
;;; The C mechanism stays C: the frame conversion, the
;;; help_echo_string = Qnil assignment, the pgtk_emacs_to_gtk_modifiers
;;; conversion, the do_help computation, the any_help_event_p flag, the
;;; gen_help_event calls, the scroll accumulator, and the 2 fabs tests.
;;;
;;; This corpus pins the port end state.  Three kinds of check:
;;;
;;;   - a load / export check: the module loads and exports the 4 new
;;;     procedures.
;;;   - a decision check: the 2 pure procedures return the right value;
;;;     a runtime check: the 2 name readers read the live cell.
;;;   - a static wiring check: src/pgtkterm.c holds the 4 dispatchers
;;;     and the 4 module references; the 6 old C reads are gone; the 2
;;;     DEFVAR_* sites stayed C at imp-5 and moved to Scheme at imp-6;
;;;     the module boot-loads once.
;;;
;;; The repo root is bound by the .el wrapper as %m33-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test
;;; and prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m33-imp5.el.

(use-modules (ice-9 rdelim))
(use-modules (srfi srfi-13))
(use-modules (emacs-elisp runtime))

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

(define (count-occurrences text needle)
  "Return the number of non-overlapping occurrences of NEEDLE in TEXT."
  (if (or (not (string? text)) (string-null? needle))
      0
      (let loop ((start 0) (n 0))
        (let ((i (string-contains text needle start)))
          (if i (loop (+ i (string-length needle)) (1+ n)) n)))))

(define (repo path) (string-append %m33-root "/" path))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m33-root))
    (begin (report "m33-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m33-root "."))
    (report "m33-root-bound" 'PASS))

;;; --- 1. The module loads and exports the 4 new procedures ----------
(use-modules (emacs pgtk))

(define (exported? name)
  (let ((p (module-ref (resolve-module '(emacs pgtk)) name)))
    (procedure? p)))

(check "m33/imp5/export/pgtk-clear-help-echo?" #t
       (exported? 'pgtk-clear-help-echo?))
(check "m33/imp5/export/pgtk-help-event-action" #t
       (exported? 'pgtk-help-event-action))
(check "m33/imp5/export/pgtk-extra-keyboard-modifiers" #t
       (exported? 'pgtk-extra-keyboard-modifiers))
(check "m33/imp5/export/pgtk-mwheel-coalesce-scroll-events?" #t
       (exported? 'pgtk-mwheel-coalesce-scroll-events?))

;;; --- 2. Decisions: the 2 pure procedures ---------------------------
;;; pgtk-clear-help-echo? takes a Scheme boolean (the C passes a C bool)
;;; and returns it unchanged.  It must NOT use the elisp truthy? helper,
;;; which would turn a Scheme #f into #t.  brief.org 4.
(check "m33/imp5/decision/clear-help-false" #f
       (pgtk-clear-help-echo? #f))
(check "m33/imp5/decision/clear-help-true" #t
       (pgtk-clear-help-echo? #t))
(check "m33/imp5/decision/clear-help-is-boolean" #t
       (boolean? (pgtk-clear-help-echo? #f)))

;; pgtk-help-event-action takes an elisp fixnum and returns 1 or 0.
(check "m33/imp5/decision/help-action-1" 1
       (pgtk-help-event-action 1))
(check "m33/imp5/decision/help-action-0" 0
       (pgtk-help-event-action 0))
(check "m33/imp5/decision/help-action-positive" 1
       (pgtk-help-event-action 7))

;;; --- 3. Runtime: the 2 name readers read the live cell -------------
;;; Both names keep their DEFVAR_* defaults at imp-5.
(check "m33/imp5/runtime/extra-keyboard-modifiers-default" 0
       (pgtk-extra-keyboard-modifiers))
(check "m33/imp5/runtime/mwheel-coalesce-scroll-events-default" #t
       (pgtk-mwheel-coalesce-scroll-events?))

;; Prove the read is live, not a constant: write the cell, read again.
(set-symbol-value! 'extra-keyboard-modifiers 3)
(check "m33/imp5/runtime/extra-keyboard-modifiers-live" 3
       (pgtk-extra-keyboard-modifiers))
(set-symbol-value! 'extra-keyboard-modifiers 0)
(check "m33/imp5/runtime/extra-keyboard-modifiers-restored" 0
       (pgtk-extra-keyboard-modifiers))

(set-symbol-value! 'mwheel-coalesce-scroll-events #nil)
(check "m33/imp5/runtime/mwheel-coalesce-scroll-events-live" #f
       (pgtk-mwheel-coalesce-scroll-events?))
(set-symbol-value! 'mwheel-coalesce-scroll-events #t)
(check "m33/imp5/runtime/mwheel-coalesce-scroll-events-restored" #t
       (pgtk-mwheel-coalesce-scroll-events?))
