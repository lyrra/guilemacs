;;; test-m19-bodies.scm --- M19 imp-1 test corpus for the Scheme ports
;;; of the 8 mlp_* geometry bodies in (emacs lispy-position).
;;;
;;; Sourced by test/keyboard/test-m19-bodies.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback from
;;; elisp.  See docs/m19-plan.org §imp-1 and brief.org.
;;;
;;; Each check compares the native Scheme port (via module-ref, since
;;; only make-lispy-position is exported) against the pre-cutover C
;;; --mlp-dispatch path for the SAME window/frame state and part.  The
;;; Scheme return values are converted to Lisp with
;;; elisp-convert-guile-object and compared with elisp-equal, so the
;;; corpus verifies byte-for-byte agreement with the C mlp_* bodies.
;;;
;;; Representative states: a plain buffer window, a window with a
;;; header-line + mode-line, a window with margins, and a window with
;;; fringes (fringe widths stay 0 on a batch build, but the C and
;;; Scheme paths must still agree).  Image-hotspot is exercised for a
;;; non-image object only; a real hotspot map needs a live image and a
;;; window system, which a batch build does not provide.

(use-modules (emacs types))        ; elisp-equal
(use-modules (emacs utils))        ; elisp-convert-guile-object
(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))

;; NB: do NOT `use-module (emacs lispy-position)' here directly — its
;; private helpers are not exported.  Access them via module-ref so we
;; can test the unexported per-region functions.

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (%sym name)
  (symbol-function name))

(define (modfn name)
  (module-ref (resolve-module '(emacs lispy-position)) name))

(define (check name expected actual)
  "Compare EXPECTED (a Lisp object from C) against ACTUAL (Scheme
return values).  ACTUAL is converted to Lisp, then compared with
elisp-equal."
  (let ((converted (elisp-convert-guile-object actual)))
    (if (elisp-equal expected converted)
        (report name 'PASS)
        (report name (list 'FAIL 'expected expected 'got converted)))))

(define (check-multi name expected thunk)
  "Compare EXPECTED (a Lisp list from C) against the multiple values
THUNK returns."
  (call-with-values thunk
    (lambda vals (check name expected vals))))

;;; --- 1. Plain buffer window ----------------------------------------
(let* ((w ((%sym 'selected-window)))
       (f ((%sym 'selected-frame)))
       (mx 10) (my 5))
  ;; fringes: left / right
  (let ((c ((%sym '--mlp-dispatch) 4 w #t mx my #nil #nil)))
    (check-multi "plain/fringes/left" c (lambda () ((modfn 'fringes) w #t mx my))))
  (let ((c ((%sym '--mlp-dispatch) 4 w #f mx my #nil #nil)))
    (check-multi "plain/fringes/right" c (lambda () ((modfn 'fringes) w #f mx my))))
  ;; scroll-border: vertical border (part 3), bottom divider (part 13)
  (let ((c ((%sym '--mlp-dispatch) 5 w 3 mx my #nil #nil)))
    (check-multi "plain/scroll/vborder" c (lambda () ((modfn 'scroll-border) w 3 mx my))))
  (let ((c ((%sym '--mlp-dispatch) 5 w 13 mx my #nil #nil)))
    (check-multi "plain/scroll/bottom" c (lambda () ((modfn 'scroll-border) w 13 mx my))))
  ;; scroll-border: vertical/horizontal scroll bar, right divider
  (let ((c ((%sym '--mlp-dispatch) 5 w 10 mx my #nil #nil)))
    (check-multi "plain/scroll/vbar" c (lambda () ((modfn 'scroll-border) w 10 mx my))))
  (let ((c ((%sym '--mlp-dispatch) 5 w 11 mx my #nil #nil)))
    (check-multi "plain/scroll/hbar" c (lambda () ((modfn 'scroll-border) w 11 mx my))))
  (let ((c ((%sym '--mlp-dispatch) 5 w 12 mx my #nil #nil)))
    (check-multi "plain/scroll/rdiv" c (lambda () ((modfn 'scroll-border) w 12 mx my))))
  ;; mode/header line: mode-line (part 2), header-line (part 4), tab-line (part 5)
  (let ((c ((%sym '--mlp-dispatch) 6 w 2 mx my #nil #nil)))
    (check-multi "plain/mode/part2" c (lambda () ((modfn 'mode-header-line) w 2 mx my))))
  (let ((c ((%sym '--mlp-dispatch) 6 w 4 mx my #nil #nil)))
    (check-multi "plain/mode/part4" c (lambda () ((modfn 'mode-header-line) w 4 mx my))))
  (let ((c ((%sym '--mlp-dispatch) 6 w 5 mx my #nil #nil)))
    (check-multi "plain/mode/part5" c (lambda () ((modfn 'mode-header-line) w 5 mx my))))
  ;; margins: left (part 8), right (part 9)
  (let ((c ((%sym '--mlp-dispatch) 7 w 8 mx my #nil #nil)))
    (check-multi "plain/margins/part8" c (lambda () ((modfn 'margins) w 8 mx my))))
  (let ((c ((%sym '--mlp-dispatch) 7 w 9 mx my #nil #nil)))
    (check-multi "plain/margins/part9" c (lambda () ((modfn 'margins) w 9 mx my))))
  ;; buffer-posn-pass: text area (part 1) — with posn = nil (the path
  ;; make-lispy-position uses on a plain click), right fringe (7),
  ;; right margin (9), vscroll (10)
  (let ((c ((%sym '--mlp-dispatch) 8 w 1 mx my 10 #nil)))
    (check-multi "plain/buffer/text" c
                 (lambda () ((modfn 'buffer-posn-pass) w 1 mx my 10 #nil))))
  (let ((c ((%sym '--mlp-dispatch) 8 w 7 mx my 10 'posn)))
    (check-multi "plain/buffer/rfringe" c
                 (lambda () ((modfn 'buffer-posn-pass) w 7 mx my 10 'posn))))
  (let ((c ((%sym '--mlp-dispatch) 8 w 9 mx my 10 'posn)))
    (check-multi "plain/buffer/rmargin" c
                 (lambda () ((modfn 'buffer-posn-pass) w 9 mx my 10 'posn))))
  (let ((c ((%sym '--mlp-dispatch) 8 w 10 mx my 10 'posn)))
    (check-multi "plain/buffer/vscroll" c
                 (lambda () ((modfn 'buffer-posn-pass) w 10 mx my 10 'posn))))
  ;; internal-border: posn non-nil -> unchanged on a no-border state
  (let ((c ((%sym '--mlp-dispatch) 1 f mx my 'foo #nil #nil)))
    (check "plain/internal/foo" c ((modfn 'internal-border) f mx my 'foo)))
  ;; image-hotspot: non-image object -> posn unchanged
  (let ((c ((%sym '--mlp-dispatch) 2 'foo 1 2 'posn #nil #nil)))
    (check "plain/img/nonimage" c ((modfn 'image-hotspot-check) 'foo 1 2 'posn)))
  ;; frame-preamble: compare against C dispatch region 3
  (let ((c ((%sym '--mlp-dispatch) 3 f mx my #nil #nil #nil)))
    (check "plain/preamble/c" c ((modfn 'frame-preamble) f mx my))))

;;; --- 2. Window with header-line + mode-line ------------------------
(let* ((w ((%sym 'selected-window)))
       (mx 30) (my 30))
  (set-symbol-value! 'header-line-format "m19-header")
  (set-symbol-value! 'mode-line-format "m19-mode")  ((%sym 'redisplay) #t)
  ;; mode-line click
  (let ((c ((%sym '--mlp-dispatch) 6 w 2 mx my #nil #nil)))
    (check-multi "header/mode/part2" c (lambda () ((modfn 'mode-header-line) w 2 mx my))))
  ;; header-line click
  (let ((c ((%sym '--mlp-dispatch) 6 w 4 mx my #nil #nil)))
    (check-multi "header/mode/part4" c (lambda () ((modfn 'mode-header-line) w 4 mx my))))
  ;; fringes still agree
  (let ((c ((%sym '--mlp-dispatch) 4 w #t mx my #nil #nil)))
    (check-multi "header/fringes/left" c (lambda () ((modfn 'fringes) w #t mx my)))))

;;; --- 3. Window with margins ----------------------------------------
(let* ((w ((%sym 'selected-window)))
       (mx 25) (my 25))
  ((%sym 'set-window-margins) w 3 3)
  ((%sym 'redisplay) #t)
  (let ((c ((%sym '--mlp-dispatch) 7 w 8 mx my #nil #nil)))
    (check-multi "margin/part8" c (lambda () ((modfn 'margins) w 8 mx my))))
  (let ((c ((%sym '--mlp-dispatch) 7 w 9 mx my #nil #nil)))
    (check-multi "margin/part9" c (lambda () ((modfn 'margins) w 9 mx my))))
  ;; buffer-posn-pass with margins — posn = nil (the make-lispy-position path)
  (let ((c ((%sym '--mlp-dispatch) 8 w 1 mx my 25 #nil)))
    (check-multi "margin/buffer/text" c
                 (lambda () ((modfn 'buffer-posn-pass) w 1 mx my 25 #nil)))))

;;; --- 4. Window with fringes ----------------------------------------
(let* ((w ((%sym 'selected-window)))
       (mx 15) (my 15))
  ((%sym 'set-window-fringes) w 5 5 #nil)
  ((%sym 'redisplay) #t)
  (let ((c ((%sym '--mlp-dispatch) 4 w #t mx my #nil #nil)))
    (check-multi "fringe/left" c (lambda () ((modfn 'fringes) w #t mx my))))
  (let ((c ((%sym '--mlp-dispatch) 4 w #f mx my #nil #nil)))
    (check-multi "fringe/right" c (lambda () ((modfn 'fringes) w #f mx my)))))

;;; --- 5. frame-preamble (non-crash / shape sanity) ------------------
(let* ((f ((%sym 'selected-frame)))
       (mx 10) (my 5))
  (let ((pre ((modfn 'frame-preamble) f mx my)))
    (report "preamble/shape" (if (and (list? pre) (= (length pre) 3)) 'PASS
                                 (list 'FAIL 'expected '(window part posn) 'got pre))))
  (let ((pre ((modfn 'frame-preamble) #nil mx my)))
    (report "preamble/nil-frame" (if (and (list? pre) (= (length pre) 3)) 'PASS
                                     (list 'FAIL 'expected '(window part posn) 'got pre)))))
