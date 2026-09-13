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
;;;     DEFVAR_* sites stay C; the module boot-loads once.
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

;;; --- 4. Static: src/pgtkterm.c holds the 4 dispatchers -------------
(define pgtk-c (slurp (repo "src/pgtkterm.c")))
(if (not pgtk-c)
    (report "m33/imp5/scan/pgtkterm.c" (cons 'FAIL "src/pgtkterm.c missing"))
    (begin
      (check "m33/imp5/pgtkterm.c/includes-guile.h" #t
             (contains? pgtk-c "#include \"guile.h\""))
      (check "m33/imp5/pgtkterm.c/defines-clear-help-echo" #t
             (contains? pgtk-c "pgtk_clear_help_echo_p (bool any_help_p)"))
      (check "m33/imp5/pgtkterm.c/defines-help-event-action" #t
             (contains? pgtk-c "pgtk_help_event_action (int do_help)"))
      (check "m33/imp5/pgtkterm.c/defines-extra-keyboard-modifiers" #t
             (contains? pgtk-c "pgtk_extra_keyboard_modifiers (void)"))
      (check "m33/imp5/pgtkterm.c/defines-mwheel-coalesce" #t
             (contains? pgtk-c "pgtk_mwheel_coalesce_scroll_events_p (void)"))
      ;; The 4 module references.
      (check "m33/imp5/pgtkterm.c/refs-clear-help-echo" #t
             (contains? pgtk-c "\"emacs pgtk\", \"pgtk-clear-help-echo?\""))
      (check "m33/imp5/pgtkterm.c/refs-help-event-action" #t
             (contains? pgtk-c "\"pgtk-help-event-action\""))
      (check "m33/imp5/pgtkterm.c/refs-extra-keyboard-modifiers" #t
             (contains? pgtk-c "\"pgtk-extra-keyboard-modifiers\""))
      (check "m33/imp5/pgtkterm.c/refs-mwheel-coalesce" #t
             (contains? pgtk-c "\"pgtk-mwheel-coalesce-scroll-events?\""))
      ;; The 6 old C reads are gone.  Assert the call-site forms, not the
      ;; bare names: a comment may keep the name, and pgtk_* embeds it.
      (check "m33/imp5/pgtkterm.c/no-old-extra-keyboard-read" #f
             (contains? pgtk-c "extra_keyboard_modifiers);"))
      (check "m33/imp5/pgtkterm.c/no-old-mwheel-read-1" #f
             (contains? pgtk-c "!mwheel_coalesce_scroll_events)"))
      (check "m33/imp5/pgtkterm.c/no-old-any-help-guard" #f
             (contains? pgtk-c "if (any_help_event_p)"))
      (check "m33/imp5/pgtkterm.c/no-old-do-help-guard" #f
             (contains? pgtk-c "if (do_help > 0)"))
      ;; The mechanism stays C.
      (check "m33/imp5/pgtkterm.c/keeps-gtk-modifiers" #t
             (contains? pgtk-c "pgtk_emacs_to_gtk_modifiers"))
      (check "m33/imp5/pgtkterm.c/keeps-gen-help-event" #t
             (contains? pgtk-c "gen_help_event"))
      (check "m33/imp5/pgtkterm.c/keeps-any-help-flag" #t
             (contains? pgtk-c "any_help_event_p = true"))
      (check "m33/imp5/pgtkterm.c/keeps-fabs-tests" #t
             (contains? pgtk-c "(fabs (delta_x) > fabs (delta_y))"))))

;;; --- 5. Static: the 2 DEFVAR_* sites stay --------------------------
(define kbd-g (slurp (repo "src/keyboard-globals.c")))
(if (not kbd-g)
    (report "m33/imp5/scan/keyboard-globals.c"
            (cons 'FAIL "src/keyboard-globals.c missing"))
    (begin
      (check "m33/imp5/keyboard-globals.c/still-defvars-extra-keyboard" #t
             (contains? kbd-g "DEFVAR_INT (\"extra-keyboard-modifiers\""))
      (check "m33/imp5/keyboard-globals.c/still-defvars-mwheel" #t
             (contains? kbd-g "DEFVAR_BOOL (\"mwheel-coalesce-scroll-events\""))))

;;; --- 6. Static: the module source ----------------------------------
(define pgtk-mod (slurp (repo "mod/emacs/pgtk.scm")))
(if (not pgtk-mod)
    (report "m33/imp5/scan/module" (cons 'FAIL "mod/emacs/pgtk.scm missing"))
    (begin
      (check "m33/imp5/module/declarative" #t
             (contains? pgtk-mod "#:declarative? #t"))
      (check "m33/imp5/module/exports-clear-help-echo" #t
             (contains? pgtk-mod "pgtk-clear-help-echo?"))
      (check "m33/imp5/module/exports-help-event-action" #t
             (contains? pgtk-mod "pgtk-help-event-action"))
      (check "m33/imp5/module/exports-extra-keyboard-modifiers" #t
             (contains? pgtk-mod "pgtk-extra-keyboard-modifiers"))
      (check "m33/imp5/module/exports-mwheel-coalesce" #t
             (contains? pgtk-mod "pgtk-mwheel-coalesce-scroll-events?"))
      (check "m33/imp5/module/reads-with-symbol-value" #t
             (contains? pgtk-mod "%symbol-value"))))

;;; --- 7. Static: boot load runs the module once ---------------------
(define load-scm (slurp (repo "prelude/load.scm")))
(if (not load-scm)
    (report "m33/imp5/scan/load.scm" (cons 'FAIL "prelude/load.scm missing"))
    (begin
      (check "m33/imp5/load.scm/registers-module" #t
             (contains? load-scm "(emacs pgtk)"))
      (check "m33/imp5/load.scm/registers-module-once" 1
             (count-occurrences load-scm "(use-modules (emacs pgtk))"))))

;;; --- 8. Static: the corpus is registered ---------------------------
(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m33/imp5/run-tests.scm/registers-el" #t
       (contains? run-tests "test-m33-imp5.el"))
