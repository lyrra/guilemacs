;;; test-m16-shims.scm --- M16 imp-1 test corpus for the C help-echo
;;; shim DEFUNs in src/keyboard.c: --ie-help-event, --position-to-time,
;;; --safe-calln-or-eval, --rc-help-echo-showing-set!, and
;;; --frame-set-mouse-moved!.
;;;
;;; Sourced by test/keyboard/test-m16-shims.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp.  See docs/m16-plan.org §imp-1 and brief.org.

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

(define (truthy? x)
  (not (eq? x #nil)))

(define (elist . items)
  (let loop ((i items))
    (if (null? i) #nil (cons (car i) (loop (cdr i))))))

(define (no-error? thunk)
  (catch #t
    (lambda () (thunk) #t)
    (lambda (key . args) (list 'error key args))))

;; HELP_EVENT kind constant — derived from C via --ie-kind-from-name so
;; the test uses the exact enum value, not a copy.
(define HELP-EVENT ((%sym '--ie-kind-from-name) 'help-echo))

;;; --- 0. Registration: all 5 shims resolve ---------------------------
(define shim-names
  '(--ie-help-event --position-to-time --safe-calln-or-eval
    --rc-help-echo-showing-set! --frame-set-mouse-moved!))
(for-each
 (lambda (n)
   (check (string-append "registered:" (symbol->string n))
          #t (not (eq? (%sym n) #nil))))
 shim-names)

;;; --- 1. --ie-help-event: field mapping + store round-trip -----------
(let* ((frame ((%sym 'selected-frame)))
       (ptr ((%sym '--kbd-store-ptr-index)))
       (ie ((%sym '--ie-help-event) frame 'my-arg 'my-x 'my-y 12345)))
  ;; Direct accessor read on the returned smob (kind always HELP_EVENT,
  ;; each Lisp argument stored verbatim).
  (check "help-event/kind" HELP-EVENT ((%sym '--ie-kind) ie))
  (check "help-event/device" #t ((%sym '--ie-device) ie))
  (check "help-event/frame-or-window" frame ((%sym '--ie-frame-or-window) ie))
  (check "help-event/arg" 'my-arg ((%sym '--ie-arg) ie))
  (check "help-event/x" 'my-x ((%sym '--ie-x) ie))
  (check "help-event/y" 'my-y ((%sym '--ie-y) ie))
  (check "help-event/timestamp" 12345 ((%sym '--ie-timestamp) ie))
  ;; Store round-trip via the production store sibling path, then read
  ;; the copy out of the ring with the ie accessors.
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ((%sym '--kbd-store-buffered-event) ie #nil)
      (let ((stored ((%sym '--kbd-event-ie) ptr)))
        (check "help-event/store-kind" HELP-EVENT ((%sym '--ie-kind) stored))
        (check "help-event/store-device" #t ((%sym '--ie-device) stored))
        (check "help-event/store-arg" 'my-arg ((%sym '--ie-arg) stored))
        (check "help-event/store-timestamp" 12345
               ((%sym '--ie-timestamp) stored))))
    (lambda () ((%sym '--kbd-set-store-ptr-index) ptr))))

;;; --- 2. --position-to-time: encode, and out-of-range signals --------
;; In-range position round-trips through --time-to-position unchanged.
(check "position-to-time/roundtrip" 100
       ((%sym '--time-to-position) ((%sym '--position-to-time) 100)))
;; Out-of-range input must signal, not silently wrap.  On this build
;; Time is int64, so INPUT_EVENT_POS_MAX equals MOST_POSITIVE_FIXNUM
;; and no fixnum can exceed it — only a bignum (non-fixnum, rejected by
;; CHECK_FIXNUM) triggers the signal here.
(check "position-to-time/out-of-range-signals" #t
       (not (eq? (no-error? (lambda ()
                              ((%sym '--position-to-time) (expt 2 62))))
                 #t)))

;;; --- 3. --safe-calln-or-eval: funcall vs eval, both contained ------
;; (a) FUNCTIONP help: called with WINDOW OBJECT POS; return unchanged.
(let ((calls #nil))
  (set-symbol-function! 'm16-help-fn
                        (lambda (w o p)
                          (set! calls (elist w o p))
                          "help-string"))
  (let* ((window ((%sym 'selected-window)))
         (object 'some-object)
         (pos 42)
         (r ((%sym '--safe-calln-or-eval)
             'm16-help-fn window object pos)))
    (check "safe-calln-or-eval/function-return" "help-string" r)
    (check "safe-calln-or-eval/function-args"
           (elist window object pos) calls)))
;; (b) non-function HELP: evaluated as a form (a literal string is a
;; self-evaluating form).
(check "safe-calln-or-eval/eval-form" "form-result"
       ((%sym '--safe-calln-or-eval) "form-result" #nil #nil 0))
;; (c) erroring function: safe_calln mutes and logs — returns nil, no
;; signal to the caller.  This is the whole reason the shim exists.
;; The function must accept the 3 args safe_calln passes (window
;; object pos), and must signal a Lisp error (via `signal`) — a raw
;; guile exception (e.g. `(error "boom")`) is a misc-error that the
;; Lisp safe-eval handler does not contain.
(let ((saw-error #nil))
  (set-symbol-function! 'm16-error-fn
                        (lambda (w o p)
                          ((%sym 'signal) 'error (elist "boom"))))
  (let ((r (no-error?
            (lambda ()
              (set! saw-error
                    ((%sym '--safe-calln-or-eval)
                     'm16-error-fn #nil #nil 0))))))
    (check "safe-calln-or-eval/error-no-signal" #t r)
    (check "safe-calln-or-eval/error-returns-nil" #nil saw-error)))

;;; --- 4. --rc-help-echo-showing-set!: shared flag write path ---------
;; Batch's selected window is a normal (non-minibuffer) window, so the
;; preserve predicate reads the flag directly.  Set on, read on; set
;; off, read off.
((%sym '--rc-help-echo-showing-set!) #t)
(check "showing-set!/on" #t
       (truthy? ((%sym '--rc-help-echo-redisplay-preserve-p))))
((%sym '--rc-help-echo-showing-set!) #nil)
(check "showing-set!/off" #nil
       ((%sym '--rc-help-echo-redisplay-preserve-p)))

;;; --- 5. --frame-set-mouse-moved!: no-crash + guard ------------------
;; some_mouse_moved's getter needs track_mouse non-nil to observe the
;; flag (batch cannot arrange that without the internal--track-mouse
;; macro), so this shim is verified as: the write path does not signal,
;; and the CHECK_FRAME guard rejects a non-frame.
(check "frame-set-mouse-moved!/no-signal" #t
       (no-error? (lambda ()
                    ((%sym '--frame-set-mouse-moved!)
                     ((%sym 'selected-frame))))))
(check "frame-set-mouse-moved!/guard-signals" #t
       (not (eq? (no-error?
                  (lambda () ((%sym '--frame-set-mouse-moved!) 42)))
                 #t)))
