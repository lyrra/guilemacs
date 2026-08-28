;;; test-m19-bodies.scm --- M19 imp-1 test corpus for the Scheme ports
;;; of the 8 mlp_* geometry bodies in (emacs lispy-position).
;;;
;;; Sourced by test/keyboard/test-m19-bodies.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback from
;;; elisp.  See docs/m19-plan.org §imp-1 and brief.org.
;;;
;;; Originally each check compared the native Scheme port against the C
;;; --mlp-dispatch path.  M19 imp-2 retired --mlp-dispatch and the 8 C
;;; mlp_* bodies (they had zero live callers after the Scheme cutover),
;;; so no C oracle remains.  This corpus now verifies, for the same
;;; representative window/frame states, that each Scheme per-region
;;; helper returns the correct value-arity and the deterministic posn
;;; symbol for its window_part — i.e. it still exercises every port
;;; against real windows/frames and catches crashes / signature or
;;; routing regressions.
;;;
;;; Representative states: a plain buffer window, a window with a
;;; header-line + mode-line, a window with margins, and a window with
;;; fringes (fringe widths stay 0 on a batch build).

(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))

;; NB: the private helpers are not exported; access them via module-ref.

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (%sym name)
  (symbol-function name))

(define (modfn name)
  (module-ref (resolve-module '(emacs lispy-position)) name))

(define (check-arity name expected-n thunk)
  "Check THUNK returns exactly EXPECTED-N values without erroring."
  (let ((ok #t) (detail #f))
    (catch #t
      (lambda ()
        (call-with-values thunk
          (lambda vals
            (if (not (= (length vals) expected-n))
                (begin (set! ok #f)
                       (set! detail (list 'expected-arity expected-n
                                          'got (length vals))))))))
      (lambda (k . a) (set! ok #f) (set! detail (list 'error k a))))
    (report name (if ok 'PASS detail))))

(define (check-first name expected thunk)
  "Check the first value THUNK returns equals EXPECTED (no error)."
  (let ((ok #t) (detail #f))
    (catch #t
      (lambda ()
        (call-with-values thunk
          (lambda (first . rest)
            (if (not (equal? expected first))
                (begin (set! ok #f)
                       (set! detail (list 'expected expected 'got first)))))))
      (lambda (k . a) (set! ok #f) (set! detail (list 'error k a))))
    (report name (if ok 'PASS detail))))

;;; --- 1. Plain buffer window ----------------------------------------
(let* ((w ((%sym 'selected-window)))
       (f ((%sym 'selected-frame)))
       (mx 10) (my 5))
  ;; fringes: left / right
  (check-first "plain/fringes/left" 'left-fringe
               (lambda () ((modfn 'fringes) w #t mx my)))
  (check-first "plain/fringes/right" 'right-fringe
               (lambda () ((modfn 'fringes) w #f mx my)))
  ;; scroll-border: vertical border (3), scroll bars (10/11), dividers (12/13)
  (check-first "plain/scroll/vborder" 'vertical-line
               (lambda () ((modfn 'scroll-border) w 3 mx my)))
  (check-first "plain/scroll/vbar" 'vertical-scroll-bar
               (lambda () ((modfn 'scroll-border) w 10 mx my)))
  (check-first "plain/scroll/hbar" 'horizontal-scroll-bar
               (lambda () ((modfn 'scroll-border) w 11 mx my)))
  (check-first "plain/scroll/rdiv" 'right-divider
               (lambda () ((modfn 'scroll-border) w 12 mx my)))
  (check-first "plain/scroll/bottom" 'bottom-divider
               (lambda () ((modfn 'scroll-border) w 13 mx my)))
  ;; mode/header/tab line
  (check-first "plain/mode/part2" 'mode-line
               (lambda () ((modfn 'mode-header-line) w 2 mx my)))
  (check-first "plain/mode/part4" 'header-line
               (lambda () ((modfn 'mode-header-line) w 4 mx my)))
  (check-first "plain/mode/part5" 'tab-line
               (lambda () ((modfn 'mode-header-line) w 5 mx my)))
  ;; margins
  (check-first "plain/margins/part8" 'left-margin
               (lambda () ((modfn 'margins) w 8 mx my)))
  (check-first "plain/margins/part9" 'right-margin
               (lambda () ((modfn 'margins) w 9 mx my)))
  ;; buffer-posn-pass: arity only (values are geometry-dependent)
  (check-arity "plain/buffer/text" 10
               (lambda () ((modfn 'buffer-posn-pass) w 1 mx my 10 #nil)))
  (check-arity "plain/buffer/rfringe" 10
               (lambda () ((modfn 'buffer-posn-pass) w 7 mx my 10 'posn)))
  (check-arity "plain/buffer/rmargin" 10
               (lambda () ((modfn 'buffer-posn-pass) w 9 mx my 10 'posn)))
  (check-arity "plain/buffer/vscroll" 10
               (lambda () ((modfn 'buffer-posn-pass) w 10 mx my 10 'posn)))
  ;; internal-border: posn non-nil -> unchanged on a no-border state
  (check-first "plain/internal/foo" 'foo
               (lambda () ((modfn 'internal-border) f mx my 'foo)))
  ;; image-hotspot: non-image object -> posn unchanged
  (check-first "plain/img/nonimage" 'posn
               (lambda () ((modfn 'image-hotspot-check) 'foo 1 2 'posn))))

;;; --- 2. Window with header-line + mode-line ------------------------
(let* ((w ((%sym 'selected-window)))
       (mx 30) (my 30))
  (set-symbol-value! 'header-line-format "m19-header")
  (set-symbol-value! 'mode-line-format "m19-mode")
  ((%sym 'redisplay) #t)
  (check-first "header/mode/part2" 'mode-line
               (lambda () ((modfn 'mode-header-line) w 2 mx my)))
  (check-first "header/mode/part4" 'header-line
               (lambda () ((modfn 'mode-header-line) w 4 mx my)))
  (check-first "header/fringes/left" 'left-fringe
               (lambda () ((modfn 'fringes) w #t mx my))))

;;; --- 3. Window with margins ----------------------------------------
(let* ((w ((%sym 'selected-window)))
       (mx 25) (my 25))
  ((%sym 'set-window-margins) w 3 3)
  ((%sym 'redisplay) #t)
  (check-first "margin/part8" 'left-margin
               (lambda () ((modfn 'margins) w 8 mx my)))
  (check-first "margin/part9" 'right-margin
               (lambda () ((modfn 'margins) w 9 mx my)))
  (check-arity "margin/buffer/text" 10
               (lambda () ((modfn 'buffer-posn-pass) w 1 mx my 25 #nil))))

;;; --- 4. Window with fringes ----------------------------------------
(let* ((w ((%sym 'selected-window)))
       (mx 15) (my 15))
  ((%sym 'set-window-fringes) w 5 5 #nil)
  ((%sym 'redisplay) #t)
  (check-first "fringe/left" 'left-fringe
               (lambda () ((modfn 'fringes) w #t mx my)))
  (check-first "fringe/right" 'right-fringe
               (lambda () ((modfn 'fringes) w #f mx my))))

;;; --- 5. frame-preamble (non-crash / shape sanity) ------------------
(let* ((f ((%sym 'selected-frame)))
       (mx 10) (my 5))
  (let ((pre ((modfn 'frame-preamble) f mx my)))
    (report "preamble/shape" (if (and (list? pre) (= (length pre) 3)) 'PASS
                                 (list 'FAIL 'expected '(window part posn) 'got pre))))
  (let ((pre ((modfn 'frame-preamble) #nil mx my)))
    (report "preamble/nil-frame" (if (and (list? pre) (= (length pre) 3)) 'PASS
                                     (list 'FAIL 'expected '(window part posn) 'got pre)))))
