(define test-results '())
(define (report name status) (set! test-results (cons (list name status) test-results)))
(define (check name expected actual)
  (if (equal? expected actual) (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))
(define (%sym name) (symbol-function name))
(define (elist . items) (let loop ((i items)) (if (null? i) #nil (cons (car i) (loop (cdr i))))))

(define shim-names
  '(--kbd-set-store-ptr-index --ie-copy --kbd-maybe-hold-keyboard-input
    --set-kboard-kbd-queue-has-data --stop-character --sys-suspend
    --handle-interrupt-normal --ie-test-event --ie-test-hold-quit))
(for-each (lambda (n) (check (string-append "registered:" (symbol->string n)) #t
                             (not (eq? (%sym n) #nil))))
          shim-names)

(let* ((src ((%sym '--ie-test-event) 1 42 64 'f-src))
       (dst ((%sym '--ie-test-hold-quit)))
       (ret ((%sym '--ie-copy) dst src)))
  ;; returns DST
  (check "ie-copy/returns-dst" #t (eq? ret dst))
  ;; every getter on DST now matches SRC
  (check "ie-copy/kind" ((%sym '--ie-kind) src) ((%sym '--ie-kind) dst))
  (check "ie-copy/code" ((%sym '--ie-code) src) ((%sym '--ie-code) dst))
  (check "ie-copy/modifiers" ((%sym '--ie-modifiers) src)
         ((%sym '--ie-modifiers) dst))
  (check "ie-copy/frame-or-window" ((%sym '--ie-frame-or-window) src)
         ((%sym '--ie-frame-or-window) dst))
  (check "ie-copy/arg" ((%sym '--ie-arg) src) ((%sym '--ie-arg) dst))
  (check "ie-copy/device" ((%sym '--ie-device) src)
         ((%sym '--ie-device) dst))
  (check "ie-copy/timestamp" ((%sym '--ie-timestamp) src)
         ((%sym '--ie-timestamp) dst))
  ;; and the values are the src ones, not dst's old (hold-quit) ones
  (check "ie-copy/kind-value" 1 ((%sym '--ie-kind) dst))
  (check "ie-copy/code-value" 42 ((%sym '--ie-code) dst))
  (check "ie-copy/frame-value" 'f-src ((%sym '--ie-frame-or-window) dst)))

;; store-ptr
(let ((saved ((%sym '--kbd-store-ptr-index))))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      (let ((target (if (= saved 0) 1 0)))
        (check "store-ptr/set-returns-nil" #nil
               ((%sym '--kbd-set-store-ptr-index) target))
        (check "store-ptr/roundtrip" target ((%sym '--kbd-store-ptr-index)))))
    (lambda () ((%sym '--kbd-set-store-ptr-index) saved)))
  (check "store-ptr/restored" saved ((%sym '--kbd-store-ptr-index))))

;; kbd-queue flag
(let* ((kb ((%sym 'current-kboard)))
       (saved-queue ((%sym 'kboard-kbd-queue) kb)))
  (dynamic-wind
    (lambda () ((%sym 'set-kboard-kbd-queue) kb #nil))
    (lambda ()
      ((%sym 'set-kboard-kbd-queue) kb (elist 'm13-queued))
      (check "kbd-queue-flag/returns-val-nil" #nil
             ((%sym '--set-kboard-kbd-queue-has-data) kb #nil))
      (check "kbd-queue-flag/pop-nil-when-unset" #nil
             ((%sym '--rc-pop-current-kboard-queue)))
      (check "kbd-queue-flag/returns-val-t" #t
             ((%sym '--set-kboard-kbd-queue-has-data) kb #t))
      (check "kbd-queue-flag/pop-head-when-set" 'm13-queued
             ((%sym '--rc-pop-current-kboard-queue))))
    (lambda () ((%sym 'set-kboard-kbd-queue) kb saved-queue))))

(check "stop-character/fixnum-shape" #t
       (integer? ((%sym '--stop-character))))

;; handle-interrupt smoke
;; handle_interrupt (false) with Vquit_flag nil must return without
;; signalling; it sets Vquit_flag = Qt as its side effect.  Use
;; --rks-vquit-flag-clear to reset both before and after.
((%sym '--rks-vquit-flag-clear))
((%sym '--handle-interrupt-normal))
((%sym '--rks-vquit-flag-clear))
(check "handle-interrupt/smoke-no-signal" #t #t)

;; hold-quit
(let* ((h1 ((%sym '--ie-test-hold-quit)))
       (h2 ((%sym '--ie-test-hold-quit))))
  (check "hold-quit/kind-reset" 0 ((%sym '--ie-kind) h2))
  (check "hold-quit/frame-nil" #nil ((%sym '--ie-frame-or-window) h2))
  (check "hold-quit/arg-nil" #nil ((%sym '--ie-arg) h2))
  (check "hold-quit/device-t" #t ((%sym '--ie-device) h2))
  ;; each call must return a fresh smob handle (ie_wrap allocates a new
  ;; SMOB), not a cached/constant one.
  (check "hold-quit/fresh-smob-per-call" #t (not (eq? h1 h2))))
