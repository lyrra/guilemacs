;;; test-m12-shims.scm --- M12 imp-1 test corpus for the C shim DEFUNs
;;;
;;; Sourced by test/keyboard/test-m12-shims.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp — Scheme format output does not reach emacs --batch
;;; stdout.
;;;
;;; Scope: the 8 imp-1 shims in src/keyboard.c (docs/m12-plan.org
;;; §imp-1): getctag prompt-tag save/set, the single-kboard flag, the
;;; kboard side-queue tail-append, the rec-free end-time deadline
;;; check, and the three tty keyboard-coding decode shims.  No
;;; blocking reads; the main-queue Scheme procedures are imp-3.

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (%sym name)
  (symbol-function name))

;; Build an elisp list: (items ... . #nil).  Scheme's `(list ...)`
;; terminates in '(), which is NOT eq? to the FFI's elisp-nil sentinel
;; #nil, so whole-list equality must be spelled against #nil.
(define (elist . items)
  (let loop ((items items))
    (if (null? items)
        #nil
        (cons (car items) (loop (cdr items))))))

;;; --- Registration ---------------------------------------------------
;;; All 8 shims must be registered as DEFUNs (syms_of_keyboard).

(define shim-names
  '(--get-ctag
    --set-ctag
    --kbd-single-kboard-p
    --kbd-enqueue-side-queue
    --timespec-expired-p
    --tty-keyboard-coding-requires-decoding-p
    --tty-keyboard-coding-raw-text-p
    --tty-decode-keyboard-bytes))

(for-each (lambda (n)
            (check (string-append "registered:" (symbol->string n)) #t
                   (not (eq? (%sym n) #nil))))
          shim-names)

;;; --- imp-1.1: getctag prompt-tag ------------------------------------

(let ((saved ((%sym '--get-ctag))))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ;; round-trip: nil -> set -> get (and set returns its arg)
      (check "ctag/set-nil" #nil ((%sym '--set-ctag) #nil))
      (check "ctag/get-nil" #nil ((%sym '--get-ctag)))
      (check "ctag/set-returns-tag" 'm12-tag ((%sym '--set-ctag) 'm12-tag))
      (check "ctag/get-roundtrip" 'm12-tag ((%sym '--get-ctag))))
    (lambda () ((%sym '--set-ctag) saved)))
  ;; save/restore bracket leaves the static as it was
  (check "ctag/restored" saved ((%sym '--get-ctag))))

;;; --- imp-1.1: single-kboard flag ------------------------------------

(let ((r ((%sym '--kbd-single-kboard-p))))
  (check "single-kboard-shape" #t (or (eq? r #t) (eq? r #nil))))

;;; --- imp-1.2: kboard side-queue append ------------------------------

(let* ((kb ((%sym 'current-kboard)))
       (saved-queue ((%sym 'kboard-kbd-queue) kb)))
  (dynamic-wind
    (lambda () ((%sym 'set-kboard-kbd-queue) kb #nil))
    (lambda ()
      ;; empty case: nil -> (event)
      (check "enqueue/returns-nil-empty" #nil
             ((%sym '--kbd-enqueue-side-queue) kb 'a))
      (check "enqueue/empty-append" (elist 'a)
             ((%sym 'kboard-kbd-queue) kb))
      ;; non-empty case: append at the tail
      (check "enqueue/returns-nil-nonempty" #nil
             ((%sym '--kbd-enqueue-side-queue) kb 'b))
      (check "enqueue/tail-append" (elist 'a 'b)
             ((%sym 'kboard-kbd-queue) kb))
      ;; kbd_queue_has_data: --rc-pop-current-kboard-queue returns the
      ;; head event (nil only when the flag is unset), so a non-nil
      ;; pop proves the append set the flag.
      (check "enqueue/has-data-flag" 'a
             ((%sym '--rc-pop-current-kboard-queue)))
      (check "enqueue/drained-head" (elist 'b)
             ((%sym 'kboard-kbd-queue) kb))
      (check "enqueue/pop-tail" 'b
             ((%sym '--rc-pop-current-kboard-queue)))
      (check "enqueue/empty-after-pop" #nil
             ((%sym 'kboard-kbd-queue) kb)))
    (lambda () ((%sym 'set-kboard-kbd-queue) kb saved-queue))))

;;; --- imp-1.3: rec-free end-time deadline ----------------------------

;; nil PTR -> nil (no deref).
(check "timespec/nil-ptr" #nil ((%sym '--timespec-expired-p) #nil))

;; expired storage pointer (epoch) -> t.
(check "timespec/expired" #t
       ((%sym '--timespec-expired-p) ((%sym '--rc-test-expired-end-time-ptr))))

;; far-future storage pointer (year ~2038) -> nil (not yet expired).
(check "timespec/far-future" #nil
       ((%sym '--timespec-expired-p) ((%sym '--rc-test-far-future-end-time-ptr))))

;;; --- imp-1.4: tty keyboard-coding decode shims ----------------------
;;; The three shims deref FRAME_TTY / TERMINAL_KEYBOARD_CODING
;;; unguarded on non-WINDOWSNT builds (Risk 4), so they are only
;;; called when --selected-frame-tty-p is t.  On a non-tty selected
;;; frame (batch / X) the registration check above is the sole
;;; assertion.

(if ((%sym '--selected-frame-tty-p))
    (begin
      (let ((r ((%sym '--tty-keyboard-coding-requires-decoding-p))))
        (check "tty/requires-decoding-shape" #t
               (or (eq? r #t) (eq? r #nil))))
      (let ((r ((%sym '--tty-keyboard-coding-raw-text-p))))
        (check "tty/raw-text-shape" #t
               (or (eq? r #t) (eq? r #nil))))
      ;; empty bytevector: n <= 0 -> nil (no decode attempted).
      (check "tty/decode-empty-bytevector" #nil
             ((%sym '--tty-decode-keyboard-bytes) (make-bytevector 0)))
      ;; one ASCII byte: nil (incomplete) or a list of fixnums.
      (let ((r ((%sym '--tty-decode-keyboard-bytes) #vu8(97))))
        (check "tty/decode-ascii-shape" #t
               (or (eq? r #nil)
                   (and (pair? r) (integer? (car r)))))))
    #t)
