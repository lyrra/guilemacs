;;; test-m34-imp1.scm --- M34 imp-1: the dispnew.c display/poll callers.
;;;
;;; brief.org (M34 imp-1) ports the decision logic of the six live
;;; display/poll call sites in src/dispnew.c into the new module
;;; (emacs display).  src/dispnew.c now calls five static dispatchers.
;;; See docs/kb.org ** M34.
;;;
;;; This corpus pins the port end state.  Two kinds of check:
;;;
;;;   - a runtime check: the module loads and exports the five
;;;     procedures; the pure timeout parse returns the expected values
;;;     (including the integral-float route, F1); and the sit_for
;;;     early-exit test, the Fredisplay body and the sit_for final input
;;;     test run (F3).  Those last calls touch the new C primitive
;;;     (--detect-input-pending-run-timers); src/emacs must be relinked,
;;;     so a guard reports them as INFO when the running binary is
;;;     stale, and asserts them otherwise.
;;;   - a static wiring check: src/dispnew.c holds the five dispatchers,
;;;     includes guile.h, and no longer calls the six old sites;
;;;     src/keyboard.c defines the one-argument primitive.
;;;
;;; The repo root is bound by the .el wrapper as %m34-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test
;;; and prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m34-imp1.el.

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

(define (count-substring text needle)
  (let loop ((start 0) (n 0))
    (let ((i (string-contains text needle start)))
      (if i (loop (+ i 1) (+ n 1)) n))))

(define (repo path) (string-append %m34-root "/" path))

(define (safe thunk)
  (catch #t
    (lambda () (cons 'ok (thunk)))
    (lambda (key . args) (cons 'error (cons key args)))))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m34-root))
    (begin (report "m34-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m34-root "."))
    (report "m34-root-bound" 'PASS))

;;; --- 1. The module loads and exports the five procedures ----------
(use-modules (emacs display))

(define display-mod (resolve-module '(emacs display)))

(define (exported? name)
  (let ((p (module-ref display-mod name)))
    (and (procedure? p) #t)))

(define (display-private name)
  (catch #t (lambda () (module-ref display-mod name)) (lambda args #f)))

(check "m34/imp1/export/sit-for-pre-wait!" #t (exported? 'sit-for-pre-wait!))
(check "m34/imp1/export/sit-for-timeout" #t (exported? 'sit-for-timeout))
(check "m34/imp1/export/sit-for-done?" #t (exported? 'sit-for-done?))
(check "m34/imp1/export/redisplay-swallow!" #t (exported? 'redisplay-swallow!))
(check "m34/imp1/export/maybe-gen-help-event!" #t
       (exported? 'maybe-gen-help-event!))

;;; --- 2. Runtime: the pure timeout parse ----------------------------
;;; The parse step does not touch the new C primitive, so assert it.
;;; The public sit-for-timeout adds the gobble side effect; report its
;;; result as INFO only.
(define parse (display-private '%sit-for-timeout-parse))
(check "m34/imp1/timeout/parse-available" #t (procedure? parse))

(if (procedure? parse)
    (begin
      (check "m34/imp1/timeout/int-zero" '(ok . #t) (safe (lambda () (parse 0))))
      (check "m34/imp1/timeout/int-neg" '(ok . #t) (safe (lambda () (parse -3))))
      (check "m34/imp1/timeout/int-sec" '(ok . (7 . 0)) (safe (lambda () (parse 7))))
      (check "m34/imp1/timeout/bignum-clamp" '(ok . (9223372036854775807 . 0))
             (safe (lambda () (parse (expt 2 100)))))
      (check "m34/imp1/timeout/t" '(ok . (0 . 0)) (safe (lambda () (parse #t))))
      (check "m34/imp1/timeout/t-sym" '(ok . (0 . 0)) (safe (lambda () (parse 't))))
      (check "m34/imp1/timeout/float-neg" '(ok . #t) (safe (lambda () (parse -0.5))))
      (check "m34/imp1/timeout/float-half" '(ok . (0 . 500000000))
             (safe (lambda () (parse 0.5))))
      ;; F1: an integral float must reach dtotimespec, not the integer
      ;; branch.  Guile's (integer? 2.0) is #t, so the integer branch
      ;; must test exact-integer?; else the parse returns (1.0 . 0) with
      ;; a flonum car that scm_to_intmax then rejects.
      (check "m34/imp1/timeout/float-int-one" '(ok . (1 . 0))
             (safe (lambda () (parse 1.0))))
      (check "m34/imp1/timeout/float-int-two" '(ok . (2 . 0))
             (safe (lambda () (parse 2.0))))
      (check "m34/imp1/timeout/float-zero" '(ok . #t)
             (safe (lambda () (parse 0.0))))
      (check "m34/imp1/timeout/float-huge"
             '(ok . (9223372036854775807 . 999999999))
             (safe (lambda () (parse 1.0e30))))
      (check "m34/imp1/timeout/bad-string" '(ok . wrong-type)
             (safe (lambda () (parse "not-a-number"))))
      (check "m34/imp1/timeout/bad-nil" '(ok . wrong-type)
             (safe (lambda () (parse #nil)))))
    (report "m34/imp1/timeout/skipped" (list 'INFO "parse not accessible")))

;;; --- 3. Runtime: public calls --------------------------------------
;;; src/emacs is relinked with the new primitive, so these execute and
;;; assert (F3): the sit_for early-exit test, the Fredisplay body, the
;;; sit_for final input test.  A guard falls back to INFO if the running
;;; binary is stale and lacks --detect-input-pending-run-timers.
;;; sit-for-timeout's decision values are pinned by the pure parse above;
;;; here it also runs the gobble side effect.
(define (lisp-bool? v) (or (eq? v #t) (eq? v #nil)))
(define runtime-ok
  (eq? (car (safe (lambda () (sit-for-pre-wait! #f)))) 'ok))

(if runtime-ok
    (begin
      (check "m34/imp1/runtime/pre-wait-false" #t
             (lisp-bool? (cdr (safe (lambda () (sit-for-pre-wait! #f))))))
      (check "m34/imp1/runtime/pre-wait-true" #t
             (lisp-bool? (cdr (safe (lambda () (sit-for-pre-wait! #t))))))
      (check "m34/imp1/runtime/redisplay-swallow" #t
             (lisp-bool? (cdr (safe (lambda () (redisplay-swallow!))))))
      (check "m34/imp1/runtime/sit-for-timeout-zero" '(ok . #t)
             (safe (lambda () (sit-for-timeout 0))))
      (check "m34/imp1/runtime/sit-for-timeout-t" '(ok . (0 . 0))
             (safe (lambda () (sit-for-timeout #t))))
      (check "m34/imp1/runtime/done-nbytes" '(ok . #t)
             (safe (lambda () (sit-for-done? 5))))
      (check "m34/imp1/runtime/done-zero" #t
             (lisp-bool? (cdr (safe (lambda () (sit-for-done? 0)))))))
    (report "m34/imp1/runtime/skipped"
            (list 'INFO "new primitive absent from running binary")))

;;; maybe-gen-help-event! with two nil help strings returns #nil without
;;; calling gen-help-event.  A non-nil help string reaches gen-help-event
;;; and returns #t; the helper needs no new primitive.
(check "m34/imp1/runtime/help-none" '(ok . #nil)
       (safe (lambda () (maybe-gen-help-event! #nil #nil #nil #nil #nil 0))))
(check "m34/imp1/runtime/help-some-true" #t
       (equal? (safe (lambda () (maybe-gen-help-event! "help" #nil #nil #nil #nil 0)))
               '(ok . #t)))

;;; --- 4. Static: the module source shapes the decisions -------------
(define display-src (slurp (repo "mod/emacs/display.scm")))
(if (not display-src)
    (report "m34/imp1/scan/module" (cons 'FAIL "mod/emacs/display.scm missing"))
    (begin
      (check "m34/imp1/module/export-names" #t
             (and (contains? display-src "sit-for-pre-wait!")
                  (contains? display-src "sit-for-timeout")
                  (contains? display-src "sit-for-done?")
                  (contains? display-src "redisplay-swallow!")
                  (contains? display-src "maybe-gen-help-event!")))
      (check "m34/imp1/module/new-primitive" #t
             (contains? display-src "%--detect-input-pending-run-timers"))
      (check "m34/imp1/module/sigio-guard-moved" #t
             (contains? display-src "--sigio-or-poll-usable-p"))
      (check "m34/imp1/module/gobble" #t (contains? display-src "gobble-input!"))
      (check "m34/imp1/module/dtotimespec" #t (contains? display-src "%dtotimespec"))
      (check "m34/imp1/module/reads-executing-kbd-macro" #t
             (contains? display-src "'executing-kbd-macro"))
      (check "m34/imp1/module/lazy-help-echo" #t
             (contains? display-src "(emacs help-echo)"))
      (check "m34/imp1/module/lazy-kbd-buffer" #t
             (contains? display-src "(emacs kbd-buffer)"))))

;;; --- 5. Static: src/dispnew.c calls the module, old sites are gone -
(define dispnew (slurp (repo "src/dispnew.c")))
(if (not dispnew)
    (report "m34/imp1/scan/dispnew.c" (cons 'FAIL "src/dispnew.c missing"))
    (begin
      (check "m34/imp1/dispnew.c/includes-guile.h" #t
             (contains? dispnew "#include \"guile.h\""))
      ;; The five static dispatchers exist.
      (check "m34/imp1/dispnew.c/dispatcher-pre-wait" #t
             (contains? dispnew "display_sit_for_pre_wait (bool do_display)"))
      (check "m34/imp1/dispnew.c/dispatcher-timeout" #t
             (contains? dispnew "display_sit_for_timeout (Lisp_Object timeout"))
      (check "m34/imp1/dispnew.c/dispatcher-done" #t
             (contains? dispnew "display_sit_for_done_p (int nbytes)"))
      (check "m34/imp1/dispnew.c/dispatcher-redisplay" #t
             (contains? dispnew "display_redisplay_swallow (void)"))
      (check "m34/imp1/dispnew.c/dispatcher-help" #t
             (contains? dispnew "display_maybe_gen_help_event (struct frame *f"))
      ;; sit_for and Fredisplay call the module.
      (check "m34/imp1/dispnew.c/sit-for-pre-wait-call" #t
             (contains? dispnew "display_sit_for_pre_wait (do_display)"))
      (check "m34/imp1/dispnew.c/sit-for-timeout-call" #t
             (contains? dispnew "display_sit_for_timeout (timeout, &sec, &nsec)"))
      (check "m34/imp1/dispnew.c/sit-for-done-call" #t
             (contains? dispnew "display_sit_for_done_p (nbytes)"))
      (check "m34/imp1/dispnew.c/redisplay-call" #t
             (contains? dispnew "display_redisplay_swallow ()"))
      (check "m34/imp1/dispnew.c/help-call" #t
             (contains? dispnew "display_maybe_gen_help_event (f, help_echo_string"))
      ;; The six old sites are gone.
      (check "m34/imp1/dispnew.c/no-old-swallow-true" #f
             (contains? dispnew "swallow_events (true);"))
      (check "m34/imp1/dispnew.c/no-old-swallow-display" #f
             (contains? dispnew "swallow_events (do_display);"))
      (check "m34/imp1/dispnew.c/no-old-detect-run-timers" #f
             (contains? dispnew "detect_input_pending_run_timers (do_display)"))
      (check "m34/imp1/dispnew.c/no-old-detect" #f
             (contains? dispnew "detect_input_pending ()"))
      (check "m34/imp1/dispnew.c/no-old-gobble" #f
             (contains? dispnew "gobble_input ();"))
      (check "m34/imp1/dispnew.c/no-old-sigio-guard" #f
             (contains? dispnew "USABLE_SIGIO"))
      (check "m34/imp1/dispnew.c/no-old-gen-help-event" #f
             (contains? dispnew "gen_help_event (help_echo_string"))
      ;; The module reads state through Scheme: one scm_c_public_ref site
      ;; per dispatcher, five in all, no more.  Count the call text, not
      ;; the bare name, so a comment that mentions scm_c_public_ref does
      ;; not break the check (F7).
      (check "m34/imp1/dispnew.c/five-public-refs" 5
             (count-substring dispnew "scm_c_public_ref (\"emacs display\""))))

;;; --- 6. Static: src/keyboard.c holds the one-argument primitive ----
(define kbd (slurp (repo "src/keyboard.c")))
(if (not kbd)
    (report "m34/imp1/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      (check "m34/imp1/keyboard.c/primitive-present" #t
             (contains? kbd "\"--detect-input-pending-run-timers\""))
      (check "m34/imp1/keyboard.c/primitive-one-arg" #t
             (contains? kbd "Sc_detect_input_pending_run_timers, 1, 1, 0"))))

;;; --- 7. Static: boot load and test registration --------------------
(define load-scm (slurp (repo "prelude/load.scm")))
(check "m34/imp1/load.scm/registers-module" #t
       (contains? load-scm "(emacs display)"))

(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m34/imp1/run-tests.scm/registers-el" #t
       (contains? run-tests "test-m34-imp1.el"))
