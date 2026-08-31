;;; test-m22-input-pending.scm --- M22 imp-1 parity corpus.
;;;
;;; M22 imp-1 moves two C bodies in src/keyboard.c to Scheme:
;;;   * get_input_pending (now (emacs read-key-sequence) get-input-pending!)
;;;   * update_recent_keys (deleted; the ring reshuffle now lives inside
;;;     (emacs recent-keys) lossage-size, using the new raw setters
;;;     --recent-keys-ring-set! / --lossage-limit-set!).
;;;
;;; get-input-pending! calls the already-live C shim --gobble-input
;;; (added at M11, NOT re-added here — see cr.org Finding 1) and the
;;; new --interrupts-deferred-p getter.  It reads quit-flag the same way
;;; command-loop.scm does, via (symbol-value 'quit-flag).
;;;
;;; Sourced by test/keyboard/test-m22-input-pending.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback from
;;; elisp.  Same harness as test-m21-read-key-sequence.scm.

(use-modules (emacs read-key-sequence))
(use-modules (emacs recent-keys))
(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))

(define test-results '())
(define (report name status)
  (set! test-results (cons (list name status) test-results)))
(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (%sym name) (symbol-function name))
(define ASCII-KEYSTROKE-EVENT (@@ (emacs kbd-buffer) ASCII-KEYSTROKE-EVENT))

;;; kbd-buffer seeding shims (same set as test-m14-predicates.scm).
(define %fetch      (delay (%sym '--kbd-fetch-ptr-index)))
(define %store      (delay (%sym '--kbd-store-ptr-index)))
(define %set-fetch  (delay (%sym '--kbd-set-fetch-ptr-index)))
(define %set-store  (delay (%sym '--kbd-set-store-ptr-index)))
(define %mk-event   (delay (%sym '--ie-test-event)))
(define %store-ev   (delay (%sym '--kbd-store-buffered-event)))

;;; recent-keys ring raw state (C-owned globals, read/write via shims).
(define %ring        (delay (%sym '--recent-keys-ring)))
(define %ring-set!   (delay (%sym '--recent-keys-ring-set!)))
(define %idx         (delay (%sym '--recent-keys-index)))
(define %idx-set!    (delay (%sym '--recent-keys-index-set!)))
(define %total       (delay (%sym '--total-keys)))
(define %total-set!  (delay (%sym '--total-keys-set!)))
(define %limit       (delay (%sym '--lossage-limit)))
(define %limit-set!  (delay (%sym '--lossage-limit-set!)))
(define %min         (delay (%sym '--min-num-recent-keys)))
(define %max         (delay (%sym '--max-num-recent-keys)))

;;; ---------------------------------------------------------------------
;;; 1. get-input-pending!
;;;
;;; Observable decision logic.  quit-flag is the fully controllable
;;; branch; the pending-event branch is driven through the kbd buffer.
;;; interrupt_input / interrupts_deferred are C globals with no setters
;;; (only getters), so the gobble-vs-skip split is not independently
;;; injectable here — the corpus pins the behavior that holds in the
;;; noninteractive batch harness (gobble runs, result reflects the state
;;; after gobble, both empty and seeded cases are covered).

;; 1a. quit-flag set -> true, regardless of kbd state.
(let* ((saved-qf (symbol-value 'quit-flag)))
  (dynamic-wind
    (lambda () (set-symbol-value! 'quit-flag 'C-g))
    (lambda () (check "m22/get-input-pending/quit-flag" #t
                      (get-input-pending! 0)))
    (lambda () (set-symbol-value! 'quit-flag saved-qf))))

;; 1b. Nothing pending, quit-flag nil -> false.
(let* ((saved-qf (symbol-value 'quit-flag))
       (saved-fetch ((force %fetch)))
       (saved-store ((force %store)))
       (base saved-fetch))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      (set-symbol-value! 'quit-flag #nil)
      ((force %set-fetch) base)
      ((force %set-store) base)
      (check "m22/get-input-pending/empty" #nil (get-input-pending! 0)))
    (lambda () ((force %set-fetch) saved-fetch)
               ((force %set-store) saved-store)
               (set-symbol-value! 'quit-flag saved-qf))))

;; 1c. Seeded keystroke, quit-flag nil -> true (readable-events path).
(let* ((saved-qf (symbol-value 'quit-flag))
       (saved-fetch ((force %fetch)))
       (saved-store ((force %store)))
       (base saved-fetch)
       (ie ((force %mk-event) ASCII-KEYSTROKE-EVENT 65 0 #nil)))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      (set-symbol-value! 'quit-flag #nil)
      ((force %set-fetch) base)
      ((force %set-store) base)
      ((force %store-ev) ie #nil)
      (check "m22/get-input-pending/seeded" #t (get-input-pending! 0)))
    (lambda () ((force %set-fetch) saved-fetch)
               ((force %set-store) saved-store)
               (set-symbol-value! 'quit-flag saved-qf))))

;; 1d. The shims get-input-pending! relies on exist and resolve.
(check "m22/get-input-pending/gobble-shim-bound"
       #t (procedure? (%sym '--gobble-input)))
(check "m22/get-input-pending/interrupts-deferred-shim-bound"
       #t (procedure? (%sym '--interrupts-deferred-p)))
(check "m22/get-input-pending/interrupt-input-shim-bound"
       #t (procedure? (%sym '--interrupt-input-p)))

;;; ---------------------------------------------------------------------
;;; 2. input-pending-p + C-g detection (behavior unchanged by the cut).
;;; input-pending-p (read-key-sequence.scm) still routes through
;;; --get-input-pending, which now lands in get-input-pending!.

;; 2a. Empty -> nil.
(let* ((saved-qf (symbol-value 'quit-flag))
       (saved-fetch ((force %fetch)))
       (saved-store ((force %store)))
       (base saved-fetch))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      (set-symbol-value! 'quit-flag #nil)
      ((force %set-fetch) base)
      ((force %set-store) base)
      (check "m22/input-pending-p/empty" #nil (input-pending-p #nil)))
    (lambda () ((force %set-fetch) saved-fetch)
               ((force %set-store) saved-store)
               (set-symbol-value! 'quit-flag saved-qf))))

;; 2b. Seeded keystroke -> t.
(let* ((saved-qf (symbol-value 'quit-flag))
       (saved-fetch ((force %fetch)))
       (saved-store ((force %store)))
       (base saved-fetch)
       (ie ((force %mk-event) ASCII-KEYSTROKE-EVENT 66 0 #nil)))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      (set-symbol-value! 'quit-flag #nil)
      ((force %set-fetch) base)
      ((force %set-store) base)
      ((force %store-ev) ie #nil)
      (check "m22/input-pending-p/seeded" #t (input-pending-p #nil)))
    (lambda () ((force %set-fetch) saved-fetch)
               ((force %set-store) saved-store)
               (set-symbol-value! 'quit-flag saved-qf))))

;; 2c. C-g detection: quit-flag set -> input-pending-p is t.
(let* ((saved-qf (symbol-value 'quit-flag)))
  (dynamic-wind
    (lambda () (set-symbol-value! 'quit-flag 'C-g))
    (lambda () (check "m22/input-pending-p/quit-flag" #t
                      (input-pending-p #nil)))
    (lambda () (set-symbol-value! 'quit-flag saved-qf))))

;;; ---------------------------------------------------------------------
;;; 3. lossage-size ring resize (the ported update_recent_keys).
;;;
;;; Helpers that install a known full ring: osize slots, each holding
;;; its slot index, next-write index 0 (so slot 0 is oldest, slot
;;; osize-1 newest), total = osize.

(define (setup-ring osize)
  (let ((v (make-vector osize #nil)))
    (let loop ((i 0))
      (when (< i osize)
        (vector-set! v i i)
        (loop (+ i 1))))
    ((force %ring-set!) v)
    ((force %total-set!) osize)
    ((force %idx-set!) 0)))

;; 3a. Grow: 300 -> 500.  All 300 recorded keys keep their order; new
;; slots 300..499 are nil; index = 300 % 500 = 300.
(setup-ring 300)
(let ((ret (lossage-size 500)))
  (check "m22/lossage/grow/returns" 500 ret)
  (let ((ring ((force %ring))))
    (check "m22/lossage/grow/size" 500 (vector-length ring))
    (check "m22/lossage/grow/first" 0 (vector-ref ring 0))
    (check "m22/lossage/grow/last-kept" 299 (vector-ref ring 299))
    (check "m22/lossage/grow/new-first-slot" #nil (vector-ref ring 300))
    (check "m22/lossage/grow/new-last-slot" #nil (vector-ref ring 499))
    (check "m22/lossage/grow/index" 300 ((force %idx)))
    (check "m22/lossage/grow/limit" 500 ((force %limit)))))

;; 3b. Shrink: 300 -> 100.  Only the newest 100 (slots 200..299) survive,
;; in order.  idx = 100 % 100 = 0.
(setup-ring 300)
(let ((ret (lossage-size 100)))
  (check "m22/lossage/shrink/returns" 100 ret)
  (let ((ring ((force %ring))))
    (check "m22/lossage/shrink/size" 100 (vector-length ring))
    (check "m22/lossage/shrink/oldest-kept" 200 (vector-ref ring 0))
    (check "m22/lossage/shrink/newest-kept" 299 (vector-ref ring 99))
    (check "m22/lossage/shrink/index" 0 ((force %idx)))
    (check "m22/lossage/shrink/limit" 100 ((force %limit)))))

;; 3c. Grow from a non-zero index: recent_keys_index is the next-write
;; slot, so order must wrap.  Ring 300 full, index 100 (newest = slot
;; 99, oldest = slot 100).  Grow to 500 keeps all 300 in order.
(let ((v (make-vector 300 #nil)))
  (let loop ((i 0))
    (when (< i 300)
      (vector-set! v i i)
      (loop (+ i 1))))
  ((force %ring-set!) v)
  ((force %total-set!) 300)
  ((force %idx-set!) 100))
(let ((ret (lossage-size 500)))
  (check "m22/lossage/grow-wrap/returns" 500 ret)
  (let ((ring ((force %ring))))
    ;; kept = total = 300.  C loop: idx = 100 - 300 + i = i - 200, wrapped
    ;; by +300 when negative.  i=0..199 -> idx 100..299 (values 100..299,
    ;; oldest first); i=200..299 -> idx 0..99 (values 0..99).  So v[0]=100,
    ;; v[199]=299, v[200]=0, v[299]=99.
    (check "m22/lossage/grow-wrap/oldest" 100 (vector-ref ring 0))
    (check "m22/lossage/grow-wrap/mid" 299 (vector-ref ring 199))
    (check "m22/lossage/grow-wrap/wrap" 0 (vector-ref ring 200))
    (check "m22/lossage/grow-wrap/newest" 99 (vector-ref ring 299))
    (check "m22/lossage/grow-wrap/new-first-slot" #nil (vector-ref ring 300))
    (check "m22/lossage/grow-wrap/index" 300 ((force %idx)))))

;; 3d. Identity: lossage-size on the current size returns it unchanged.
((force %limit-set!) 300)
(setup-ring 300)
(check "m22/lossage/identity" 300 (lossage-size 300))

;; 3e. Bound guard: below the min is rejected (signals user-error).
((force %limit-set!) 300)
(setup-ring 300)
(let ((raised #f))
  (catch #t
    (lambda () (lossage-size (- ((force %min)) 1)))
    (lambda (key . args) (set! raised #t)))
  (check "m22/lossage/below-min-rejected" #t raised))
