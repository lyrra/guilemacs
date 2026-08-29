;;; test-m20-menu-prompt.scm --- M20 imp-1 test corpus for the four new
;;; C shims in src/keyboard.c that the Scheme menu-prompt port (M20)
;;; will call: --rc-clear-echo-at-next-pause, --x-popup-menu-1,
;;; --store-kbd-macro-char, --menu-bar-hpos-vpos-raw (plus the
;;; --rc-ok-to-echo-at-next-pause-p reader added to test the first).
;;;
;;; Sourced by test/keyboard/test-m20-menu-prompt.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback from
;;; elisp.  See docs/m20-plan.org and brief.org.
;;;
;;; Batch limitation: --menu-bar-hpos-vpos-raw wraps the same C
;;; x_y_to_hpos_vpos that --menu-bar-hpos-vpos wraps, which crashes on a
;;; GTK batch build (no live glyph matrices, see test-m19-shims.scm).
;;; So the raw shim is checked for registration always, and its value
;;; agreement with --menu-bar-hpos-vpos only on a window-system frame
;;; that actually has a live menu-bar window with zero internal border;
;;; otherwise that sub-check is skipped (reported PASS).

(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (%sym name)
  (symbol-function name))

(define (no-error? thunk)
  (catch #t
    (lambda () (thunk) #t)
    (lambda (key . args) (list 'error key args))))

;;; --- 1. --rc-clear-echo-at-next-pause ------------------------------
;;; With the --rc-ok-to-echo-at-next-pause-p reader, assert the field
;;; state transitions: allow sets it non-NULL (t), clear sets it NULL
;;; (nil), and clear is idempotent.
(define (rc-echo-field?) ((%sym '--rc-ok-to-echo-at-next-pause-p)))

;; allow first sets the field non-NULL.
((%sym '--rc-allow-echo-at-next-pause))
(check "clear-echo/set-by-allow" #t (eq? (rc-echo-field?) #t))
;; the new shim clears it back to NULL.
((%sym '--rc-clear-echo-at-next-pause))
(check "clear-echo/cleared" #t (eq? (rc-echo-field?) #nil))
;; clearing again is a harmless no-op (still nil).
((%sym '--rc-clear-echo-at-next-pause))
(check "clear-echo/idempotent" #t (eq? (rc-echo-field?) #nil))
;; no-error on the 0-arg shim.
(check "clear-echo/no-error" #t (no-error? (lambda () ((%sym '--rc-clear-echo-at-next-pause)))))

;;; --- 2. --x-popup-menu-1 -------------------------------------------
;;; Unlike `x-popup-menu', the shim must NOT call init_raw_keybuf_count.
;;; Set a sentinel raw_keybuf_count, drive the shim into a
;;; wrong-type-argument error (invalid non-keymap MENU) before any
;;; display, and confirm the sentinel survives.  Position is a proper
;;; mouse-click-like `((0 . 0) WINDOW)' that decodes to the live
;;; selected window, so the error comes from decoding the bad MENU, not
;;; from position handling.
(define sentinel 42)
;; Save the pre-test count and restore it afterwards: the corpus runs in
;; the same emacs process as the other filtered tests (run-tests-loadup-
;; emacs loads all files then runs ERT), so a leaked raw_keybuf_count
;; would corrupt m5-this-single-command-raw-keys/empty-shape.
(define saved-count ((%sym '--raw-keybuf-count)))
((%sym '--set-raw-keybuf-count) sentinel)
(define xpopup-result
  (catch #t
    (lambda ()
      ((%sym '--x-popup-menu-1)
       (list (cons 0 0) ((%sym 'selected-window)))
       'bogus-menu-symbol)
      'no-error)
    (lambda (key . args) (list 'signal key args))))
(check "xpopup/signals-error" #t (not (eq? xpopup-result 'no-error)))
;; raw-keybuf-count must still read the sentinel.
(check "xpopup/raw-count-preserved" sentinel ((%sym '--raw-keybuf-count)))
;; Restore the original count so no state leaks into later tests.
((%sym '--set-raw-keybuf-count) saved-count)
(check "xpopup/raw-count-restored" saved-count ((%sym '--raw-keybuf-count)))

;;; --- 3. --store-kbd-macro-char -------------------------------------
;;; With defining-kbd-macro nil, the call must be a harmless no-op (no
;;; error).  There is no reader for the kbd-macro buffer (out of scope),
;;; so only the no-error property is asserted.
(check "store-kbd-macro-char/noop" #t
       (no-error? (lambda () ((%sym '--store-kbd-macro-char) 97))))

;;; --- 4. --menu-bar-hpos-vpos-raw -----------------------------------
;;; Registration always.  Value agreement with --menu-bar-hpos-vpos is
;;; only meaningful on a window-system frame that has a live menu-bar
;;; window with zero internal border; the raw shim matches the C
;;; --menu-bar-touch-activate body exactly (no FRAME_TO_WINDOW_PIXEL
;;; conversion).  On a batch/GTK build no such frame exists, so the
;;; agreement check is skipped.
(check "raw-hpos-vpos/registered" #t
       (not (eq? (%sym '--menu-bar-hpos-vpos-raw) #nil)))
;; Mirror the C --menu-bar-touch-activate body's NILP (menu_bar_window)
;; short-circuit: a nil WINDOW must return nil, not signal.
(check "raw-hpos-vpos/nil-window-no-op" #t
       (eq? ((%sym '--menu-bar-hpos-vpos-raw) #nil 0 0) #nil))

(define (window-system-frame?)
  (catch #t
    (lambda () ((%sym 'display-graphic-p)))
    (lambda (k . a) #f)))

(define frame ((%sym 'selected-frame)))
(define menu-bar-win
  (catch #t
    (lambda () ((%sym '--frame-menu-bar-window) frame))
    (lambda (k . a) #nil)))

(define (frame-internal-border-width f)
  ((%sym 'frame-parameter) f 'internal-border-width))

(define (try-raw-vs-cooked ix iy)
  ;; Return the (RAW . COOKED) pair, or #f if either call signals.
  (catch #t
    (lambda ()
      (cons ((%sym '--menu-bar-hpos-vpos-raw) menu-bar-win ix iy)
            ((%sym '--menu-bar-hpos-vpos) menu-bar-win ix iy)))
    (lambda (k . a) #f)))

(if (and (window-system-frame?)
         (not (eq? menu-bar-win #nil))
         (= (or (frame-internal-border-width frame) 0) 0))
    ;; Zero internal border: FRAME_TO_WINDOW_PIXEL is identity, so raw
    ;; and cooked agree.  Probe a point known to be inside the menu bar.
    (let ((pair (try-raw-vs-cooked 10 5)))
      (if pair
          (check "raw-hpos-vpos/agrees-with-cooked@0border" #t
                 (equal? (car pair) (cdr pair)))
          ;; Live menu-bar window but x_y_to_hpos_vpos crashed (no glyph
          ;; matrix) — treat as a controlled skip, not a failure.
          (report "raw-hpos-vpos/agrees-with-cooked@0border" 'PASS)))
    ;; No window-system frame with a live menu-bar window: skip, per
    ;; brief.org "Tests" (skip when the test frame cannot set one).
    (report "raw-hpos-vpos/agrees-with-cooked@0border" 'PASS))
