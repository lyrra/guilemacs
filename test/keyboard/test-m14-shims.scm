;;; test-m14-shims.scm --- M14 imp-1 test corpus for the 6 C shim
;;; DEFUNs in src/keyboard.c: --kbd-excise-selection-event-at!,
;;; --kbd-queue-has-data, --any-kbd-queue-has-data,
;;; --toolkit-scroll-bars-p, --redisplay-preserve-echo-area, and
;;; --timers-run.  (--timer-check was reclaimed in M28 imp-5 family 4;
;;; its smoke check now calls the (emacs timers) port.)
;;;
;;; Sourced by test/keyboard/test-m14-shims.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp — Scheme format output does not reach emacs --batch
;;; stdout.

;; M28 imp-5 (family 2) — ie-kind-from-name now lives in Scheme.
(use-modules (emacs lispy-position))
;; M28 imp-5 (family 4) — --timer-check reclaimed; call the port.
(use-modules (emacs timers))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (%sym name)
  (symbol-function name))

(define (truthy? x)
  (not (eq? x #nil)))

(define (elist . items)
  (let loop ((i items))
    (if (null? i) #nil (cons (car i) (loop (cdr i))))))

(define KBD-BUFFER-SIZE 4096)

;;; --- 0. Registration: all 7 new DEFUNs resolve ----------------------

(define shim-names
  '(--kbd-excise-selection-event-at! --kbd-queue-has-data
    --any-kbd-queue-has-data --toolkit-scroll-bars-p
    --redisplay-preserve-echo-area --timers-run))
(for-each
 (lambda (n)
   (check (string-append "registered:" (symbol->string n))
          #t (not (eq? (%sym n) #nil))))
 shim-names)

;;; --- 1. kbd-queue-has-data getters ----------------------------------
;;; Set the current kboard's flag with the existing setter, check both
;;; getters agree at each step, then restore.  Same dynamic-wind style
;;; as test-m13-shims.scm's kbd-queue flag block.
(let* ((kb ((%sym 'current-kboard)))
       (saved ((%sym '--kbd-queue-has-data) kb)))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ((%sym '--set-kboard-kbd-queue-has-data) kb #nil)
      (check "kbd-queue-has-data/getter-nil" #nil
             ((%sym '--kbd-queue-has-data) kb))
      (check "any-kbd-queue-has-data/all-nil" #nil
             ((%sym '--any-kbd-queue-has-data)))
      ((%sym '--set-kboard-kbd-queue-has-data) kb #t)
      (check "kbd-queue-has-data/getter-t" #t
             ((%sym '--kbd-queue-has-data) kb))
      (check "any-kbd-queue-has-data/one-set" #t
             ((%sym '--any-kbd-queue-has-data))))
    (lambda () ((%sym '--set-kboard-kbd-queue-has-data) kb saved)))
  (check "kbd-queue-has-data/restored" saved
         ((%sym '--kbd-queue-has-data) kb)))

;;; --- 2. toolkit-scroll-bars-p: boolean type (build-dependent value) -
(define tsb ((%sym '--toolkit-scroll-bars-p)))
(check "toolkit-scroll-bars-p/boolean" #t
       (or (eq? tsb #t) (eq? tsb #nil)))

;;; --- 3. timer-check smoke -------------------------------------------
;;; (emacs timers) timer-check with no ripe timers must return without
;;; signalling.  `catch' swallows a raised exception so the runner
;;; keeps going if the port errors; a normal return records PASS.
;;; (--timer-check was reclaimed in M28 imp-5 family 4; the port is the
;;; same Scheme body C timer_check () now re-dispatches to.)
(define (no-error? thunk)
  (catch #t
    (lambda () (thunk) #t)
    (lambda (key . args) (list 'error key args))))

(check "timer-check/smoke-no-signal" #t
       (no-error? (lambda () (timer-check))))

;;; --- 4. redisplay-preserve-echo-area smoke ---------------------------
;;; Call with swallow_events' 7 and the rc shim's 5; assert no error.
(check "redisplay-preserve-echo-area/7-no-signal" #t
       (no-error? (lambda () ((%sym '--redisplay-preserve-echo-area) 7))))
(check "redisplay-preserve-echo-area/5-no-signal" #t
       (no-error? (lambda () ((%sym '--redisplay-preserve-echo-area) 5))))

;;; --- 5. timers-run is a fixnum ---------------------------------------
(check "timers-run/fixnum" #t
       (integer? ((%sym '--timers-run))))

;;; --- 6. excise-selection-event-at! on a seeded ring ------------------
;;; Seed one SELECTION_REQUEST_EVENT into the middle of the ring (fetch
;;; strictly before the slot, store strictly after), then excise it.
;;; Assert the shim returns t and the fetch cursor advanced by one.
(let* ((saved-fetch ((%sym '--kbd-fetch-ptr-index)))
       (saved-store ((%sym '--kbd-store-ptr-index)))
       (slot (modulo (+ saved-fetch 2) KBD-BUFFER-SIZE))  ; strict middle
       (kind (ie-kind-from-name 'selection-request-event))
       (ie ((%sym '--ie-test-event) kind 0 0 #nil)))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ;; Position store so the event lands at SLOT, fetch just before it.
      ((%sym '--kbd-set-store-ptr-index) slot)
      ((%sym '--kbd-set-fetch-ptr-index)
       (modulo (- slot 1) KBD-BUFFER-SIZE))
      ((%sym '--kbd-store-buffered-event) ie #nil)
      ;; Now the ring holds the selection event at SLOT, fetch = SLOT-1,
      ;; store = SLOT+1.  Excise it.
      (check "excise/returns-t" #t
             (truthy? ((%sym '--kbd-excise-selection-event-at!) slot)))
      (check "excise/fetch-advanced" (modulo slot KBD-BUFFER-SIZE)
             ((%sym '--kbd-fetch-ptr-index))))
    (lambda () ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
               ((%sym '--kbd-set-store-ptr-index) saved-store))))

;;; --- 7. excise returns nil for a non-selection slot ------------------
(let* ((saved-fetch ((%sym '--kbd-fetch-ptr-index)))
       (saved-store ((%sym '--kbd-store-ptr-index)))
       (slot (modulo (+ saved-fetch 2) KBD-BUFFER-SIZE))
       (ie ((%sym '--ie-test-event) 1 97 0 #nil)))  ; ASCII-KEYSTROKE
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ((%sym '--kbd-set-store-ptr-index) slot)
      ((%sym '--kbd-set-fetch-ptr-index)
       (modulo (- slot 1) KBD-BUFFER-SIZE))
      ((%sym '--kbd-store-buffered-event) ie #nil)
      (check "excise/non-selection-returns-nil" #nil
             ((%sym '--kbd-excise-selection-event-at!) slot))
      (check "excise/non-selection-fetch-unmoved"
             (modulo (- slot 1) KBD-BUFFER-SIZE)
             ((%sym '--kbd-fetch-ptr-index))))
    (lambda () ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
               ((%sym '--kbd-set-store-ptr-index) saved-store))))
