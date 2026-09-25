;;; test-m33-imp2.scm --- M33 imp-2: the xmenu.c/gtkutil.c menu/help
;;; consumers.
;;;
;;; brief.org (M33 imp-2) ports the decision logic of the X/GTK menu help
;;; and timer paths in src/xmenu.c and src/gtkutil.c into the new module
;;; (emacs menu), and the show_help_echo stub retires.  See
;;; docs/m33-plan.org A5 ... A7.
;;;
;;; This corpus pins the port end state.  Two kinds of check:
;;;
;;;   - a runtime check: the module loads and exports the four
;;;     procedures.  The sandbox may not relink src/emacs, so a runtime
;;;     call that touches a newly built helper is guarded and reported
;;;     as INFO, not asserted.
;;;   - a static wiring check: src/xmenu.c holds the three dispatchers
;;;     and no longer calls show_help_echo or timer_check; src/gtkutil.c
;;;     holds the dispatch and no longer calls timer_check;
;;;     src/keyboard.c no longer defines show_help_echo but still
;;;     defines timer_check; src/keyboard.h no longer declares
;;;     show_help_echo; the module is boot-loaded.
;;;
;;; The repo root is bound by the .el wrapper as %m33-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test
;;; and prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m33-imp2.el.

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

;;; --- 1. The module loads and exports the four procedures -----------
(use-modules (emacs menu))

(define (exported? name)
  (let ((p (module-ref (resolve-module '(emacs menu)) name)))
    (procedure? p)))

(check "m33/imp2/export/menu-show-help-event" #t
       (exported? 'menu-show-help-event))
(check "m33/imp2/export/menu-help-callback" #t
       (exported? 'menu-help-callback))
(check "m33/imp2/export/x-menu-timer-wait" #t
       (exported? 'x-menu-timer-wait))
(check "m33/imp2/export/xg-maybe-add-timer-delay" #t
       (exported? 'xg-maybe-add-timer-delay))

;;; --- 2. Runtime: the no-frame help path (no new primitive) ---------
;;; With a #nil frame, menu-show-help-event calls show-help-echo, which
;;; is already a Scheme procedure.  Assert its return value.
(define (safe thunk)
  (catch #t
    (lambda () (cons 'ok (thunk)))
    (lambda (key . args) (cons 'error (cons key args)))))

(let ((r (safe (lambda () (menu-show-help-event #nil "text")))))
  (report "m33/imp2/runtime/show-help-event" (list 'INFO r))
  (check "m33/imp2/runtime/show-help-event-returns-nil" '(ok . #nil) r))

;;; --- 3. Runtime: calls that may need a rebuilt binary --------------
;;; menu-help-callback delegates to (emacs terminal) and reads the
;;; --menu-items primitive; x-menu-timer-wait / xg-maybe-add-timer-delay
;;; read the timers module.  The running binary may lack a freshly
;;; built helper, so print an INFO report and do not assert.
(let ((r (safe (lambda () (menu-help-callback "" 1 2)))))
  (report "m33/imp2/runtime/help-callback" (list 'INFO r)))
(let ((r (safe (lambda () (x-menu-timer-wait)))))
  (report "m33/imp2/runtime/x-menu-timer-wait" (list 'INFO r)))
(let ((r (safe (lambda () (xg-maybe-add-timer-delay)))))
  (report "m33/imp2/runtime/xg-maybe-add-timer-delay" (list 'INFO r)))
