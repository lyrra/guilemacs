;;; test-kbd-mouse-motion.scm --- M11 imp-4 mouse-motion-fallback test
;;; corpus for (emacs kbd-buffer)
;;;
;;; Sourced by test/keyboard/test-kbd-mouse-motion.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp — Scheme format output does not reach emacs --batch
;;; stdout.
;;;
;;; On the CI termcap build --mouse-position-hook returns nil and
;;; --some-mouse-moved is nil (no window system), so the full
;;; mouse-motion-synthesize! path is not reachable.  Instead we test
;;; (a) registration of the imp-4 DEFUNs, (b) the "wired" property
;;; (mouse-motion-synthesize! is a real procedure, not the old
;;; throwing stub), and (c) the pure construction helpers, including
;;; the F2 regression that --make-lispy-position accepts a nil frame.

(use-modules (emacs kbd-buffer))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (%sym name)
  (symbol-function name))

;; mouse-motion-synthesize! is module-private; reach it through @@
;; (same idiom as test-kbd-dispatch.scm's dispatch-event!).
(define mouse-motion-synthesize! (@@ (emacs kbd-buffer) mouse-motion-synthesize!))

;;; --- 1. Registration of the imp-4 DEFUNs -----------------------------

(for-each (lambda (n)
            (check (string-append "registered:" (symbol->string n)) #t
                   (not (eq? (%sym n) #nil))))
          '(--mouse-position-hook
            --frame-last-mouse-device
            --kbd-abort
            --make-lispy-position
            --make-scroll-bar-position))

;;; --- 2. Wired (no longer the not-implemented stub) -------------------

(check "wired/mouse-motion-synthesize!" #t
       (procedure? mouse-motion-synthesize!))

;;; --- 3. --frame-last-mouse-device (GAP 1) ----------------------------

;; Non-frame input must return nil (no XFRAME abort).
(check "frame-last-mouse-device/non-frame" #nil
       ((%sym '--frame-last-mouse-device) 4242))
(check "frame-last-mouse-device/nil" #nil
       ((%sym '--frame-last-mouse-device) #nil))

;;; --- 4. --make-lispy-position nil tolerance (F2 regression) ----------

;; C make_lispy_position (keyboard.c:7388) handles f == NULL by passing
;; Qnil; the DEFUN must forward a nil FOW instead of XFRAME-aborting.
(let ((r ((%sym '--make-lispy-position) #nil 10 20 100)))
  (check "make-lispy-position/nil-frame-returns-list" #t (list? r))
  (check "make-lispy-position/nil-frame-shape" 4 (length r))
  (check "make-lispy-position/nil-frame-car" #nil (car r)))

;;; --- 5. --make-scroll-bar-position pure shape (brief.org step 5) -----

;; list5 (FOW TYPE (X . Y) TIMESTAMP PART-SYM); part index 1 maps to
;; `above-handle' via scroll_bar_parts (keyboard.c:7053).
(let ((r ((%sym '--make-scroll-bar-position)
          'sentinel 10 20 100 1 'vertical-scroll-bar)))
  (check "make-scroll-bar-position/length" 5 (length r))
  (check "make-scroll-bar-position/fow" 'sentinel (car r))
  (check "make-scroll-bar-position/type" 'vertical-scroll-bar (cadr r))
  (check "make-scroll-bar-position/xy" (cons 10 20) (caddr r))
  (check "make-scroll-bar-position/timestamp" 100 (cadddr r))
  (check "make-scroll-bar-position/part-symbol" 'above-handle
         (car (cddddr r))))
