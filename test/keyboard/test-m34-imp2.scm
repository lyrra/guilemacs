;;; test-m34-imp2.scm --- M34 imp-2: the frame.c swallow and single-kboard
;;;                       callers.
;;;
;;; brief.org (M34 imp-2) ports the decision logic of the two live
;;; src/frame.c call sites of keyboard extern stubs into the new module
;;; (emacs frame).  src/frame.c now calls two static dispatchers; no stub
;;; retires.  See docs/kb.org ** M34.
;;;
;;; This corpus pins the port end state.  Two kinds of check:
;;;
;;;   - a runtime check: the module loads and exports the two procedures;
;;;     and frame-maybe-not-single-kboard-state! runs the non-nil arm (no
;;;     side effect, calls nothing).  The nil arm is NOT run: it clears
;;;     the single-kboard flag and leaks state into later corpora (kb
;;;     shared-harness-cross-corpus-state-leak).  Site 1 is not reachable
;;;     (no HAVE_PGTK), so it has no runtime check.
;;;   - a static wiring check: src/frame.c holds the two dispatchers,
;;;     includes guile.h, calls them, and no longer calls the two old
;;;     sites; src/keyboard.c retired not_single_kboard_state at imp-7
;;;     and make_kboard_smob is exposed with a declaration in guile.h.
;;;
;;; The repo root is bound by the .el wrapper as %m34-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test and
;;; prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m34-imp2.el.

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

;;; --- 1. The module loads and exports the two procedures ------------
(use-modules (emacs frame))

(define frame-mod (resolve-module '(emacs frame)))

(define (exported? name)
  (let ((p (module-ref frame-mod name)))
    (and (procedure? p) #t)))

(check "m34/imp2/export/frame-swallow-events!" #t
       (exported? 'frame-swallow-events!))
(check "m34/imp2/export/frame-maybe-not-single-kboard-state!" #t
       (exported? 'frame-maybe-not-single-kboard-state!))

;;; --- 2. Runtime: the non-nil arm of site 2 -------------------------
;;; With FRAME-ON-SAME-KBOARD non-nil the decision calls nothing, so it
;;; has no side effect.  Pass a BOGUS kboard: not-single-kboard-state
;;; reaches kboard-eq, whose CHECK_KBOARD signals on a non-kboard.  So
;;; "no error" proves the non-nil arm never touches the kboard (cr.org
;;; 5.3).  Do NOT run the nil arm: it clears the single-kboard flag and
;;; leaks state into later corpora.  Report it as INFO.  Site 1 is not
;;; reachable (no HAVE_PGTK).
(define maybe-not-single frame-maybe-not-single-kboard-state!)

(check "m34/imp2/runtime/maybe-non-nil-no-error" 'ok
       (car (safe (lambda () (maybe-not-single "bogus-kboard" 1)))))
(check "m34/imp2/runtime/maybe-non-nil-sym" 'ok
       (car (safe (lambda () (maybe-not-single "bogus-kboard" 'some-frame)))))

(report "m34/imp2/runtime/maybe-nil-skipped"
        (list 'INFO "nil arm clears the single-kboard flag; skipped"))

;;; --- 3. Static: the module source shapes the decisions -------------
(define frame-src (slurp (repo "mod/emacs/frame.scm")))
(if (not frame-src)
    (report "m34/imp2/scan/module" (cons 'FAIL "mod/emacs/frame.scm missing"))
    (begin
      (check "m34/imp2/module/export-names" #t
             (and (contains? frame-src "frame-swallow-events!")
                  (contains? frame-src "frame-maybe-not-single-kboard-state!")))
      (check "m34/imp2/module/lazy-kbd-buffer" #t
             (contains? frame-src "(emacs kbd-buffer)"))
      (check "m34/imp2/module/lazy-single-kboard" #t
             (contains? frame-src "(emacs single-kboard)"))
      (check "m34/imp2/module/nil-test" #t (contains? frame-src "%nilp"))))

;;; --- 4. Static: src/frame.c calls the module, old sites are gone ---
(define frame-c (slurp (repo "src/frame.c")))
(if (not frame-c)
    (report "m34/imp2/scan/frame.c" (cons 'FAIL "src/frame.c missing"))
    (begin
      (check "m34/imp2/frame.c/includes-guile.h" #t
             (contains? frame-c "#include \"guile.h\""))
      ;; The two static dispatchers exist.
      (check "m34/imp2/frame.c/dispatcher-swallow" #t
             (contains? frame-c "frame_swallow_events (void)"))
      (check "m34/imp2/frame.c/dispatcher-maybe-not-single" #t
             (contains? frame-c "frame_maybe_not_single_kboard_state ("))
      ;; The two sites call the dispatchers.
      (check "m34/imp2/frame.c/swallow-call" #t
             (contains? frame-c "frame_swallow_events ();"))
      (check "m34/imp2/frame.c/maybe-not-single-call" #t
             (contains? frame-c "frame_maybe_not_single_kboard_state (kb, frame_on_same_kboard)"))
      ;; The two old sites are gone.
      (check "m34/imp2/frame.c/no-old-swallow" #f
             (contains? frame-c "swallow_events (false);"))
      (check "m34/imp2/frame.c/no-old-not-single" #f
             (contains? frame-c "not_single_kboard_state (kb);"))
      ;; The module reads state through Scheme: one scm_c_public_ref site
      ;; per dispatcher, two in all, no more.  Count the call text, not the
      ;; bare name, so a comment that mentions scm_c_public_ref does not
      ;; break the check (F7, cf. cr-m34-imp1-response.org).
      (check "m34/imp2/frame.c/two-public-refs" 2
             (count-substring frame-c "scm_c_public_ref (\"emacs frame\""))))

;;; --- 5. Static: src/keyboard.c keeps the stub, exposes the smob ----
(define kbd (slurp (repo "src/keyboard.c")))
(if (not kbd)
    (report "m34/imp2/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      ;; M34 imp-7 retired the stub (its last caller, frame.c, left C
      ;; at this imp).  The definition is gone.
      (check "m34/imp2/keyboard.c/not-single-retired" #f
             (contains? kbd "not_single_kboard_state (KBOARD *kboard)"))
      (check "m34/imp2/keyboard.c/make-kboard-smob-not-static" #f
             (contains? kbd "static SCM\nmake_kboard_smob"))))

(define guile-h (slurp (repo "src/guile.h")))
(if (not guile-h)
    (report "m34/imp2/scan/guile.h" (cons 'FAIL "src/guile.h missing"))
    (check "m34/imp2/guile.h/make-kboard-smob-decl" #t
           (contains? guile-h "extern SCM make_kboard_smob (KBOARD *kb);")))

;;; --- 6. Static: boot load and test registration --------------------
(define load-scm (slurp (repo "prelude/load.scm")))
(check "m34/imp2/load.scm/registers-module" #t
       (contains? load-scm "(emacs frame)"))

(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m34/imp2/run-tests.scm/registers-el" #t
       (contains? run-tests "test-m34-imp2.el"))
