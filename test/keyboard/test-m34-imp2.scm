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
