;;; test-m16-help-echo.scm --- M16 imp-3 test corpus for the C-to-Scheme
;;; cutover of show_help_echo, gen_help_event, and kbd_buffer_store_help_event.
;;;
;;; Sourced by test/keyboard/test-m16-help-echo.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp.  See docs/m16-plan.org §imp-3 and brief.org.
;;;
;;; imp-3 turns the three C bodies into thin dispatchers into (emacs
;;; help-echo).  The C gen-help-event / store-help-event entry points are
;;; only reachable from C callers, so the Scheme bodies are exercised
;;; directly (round-trip + x-field rule) exactly as at imp-2, while the
;;; show_help_echo dispatcher is driven through the real C entry point
;;; --rc-show-help-echo (keyboard.c), which now forwards to Scheme.  Every
;;; sub-test that advances the store pointer or mutates shared state runs
;;; inside a dynamic-wind that restores it.

(use-modules (emacs help-echo))

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

;; HELP_EVENT kind constant — derived from C so the test uses the exact
;; enum value, not a copy (same as test-m16-bodies.scm).
(define HELP-EVENT ((%sym '--ie-kind-from-name) 'help-echo))

;;; --- 0. Registration: the dispatchers' Scheme targets resolve -------
(for-each
 (lambda (n)
   (check (string-append "proc:" (symbol->string n))
          #t (procedure? (module-ref (resolve-module '(emacs help-echo)) n))))
 '(show-help-echo gen-help-event store-help-event))

;;; --- 1. gen-help-event: field mapping ------------------------------
;;; Window case: x = WINDOW.  Frame-fallback case: x = FRAME.  (Same
;;; assertions as imp-2 — these run the Scheme body the C dispatcher
;;; now forwards to.)
(define (stored-ie-after store-thunk)
  "Run STORE-THUNK, then read the ring slot it just appended at the
pre-call store index.  Restores the store pointer afterwards."
  (let ((ptr ((%sym '--kbd-store-ptr-index))))
    (dynamic-wind
      (lambda () #f)
      (lambda ()
        (store-thunk)
        ((%sym '--kbd-event-ie) ptr))
      (lambda () ((%sym '--kbd-set-store-ptr-index) ptr)))))

(let* ((frame ((%sym 'selected-frame)))
       (window ((%sym 'selected-window)))
       (obj 'some-object)
       (stored (stored-ie-after
                (lambda () (gen-help-event "help-w" frame window obj 10)))))
  (check "gen/window-kind" HELP-EVENT ((%sym '--ie-kind) stored))
  (check "gen/window-frame-or-window" frame ((%sym '--ie-frame-or-window) stored))
  (check "gen/window-arg" obj ((%sym '--ie-arg) stored))
  (check "gen/window-x" window ((%sym '--ie-x) stored))
  (check "gen/window-y" "help-w" ((%sym '--ie-y) stored))
  ;; timestamp encodes POS; round-trips back to POS via --time-to-position.
  (check "gen/window-timestamp-roundtrip" 10
         ((%sym '--time-to-position) ((%sym '--ie-timestamp) stored))))

;; Frame-fallback: a non-window (nil) for WINDOW makes x = FRAME.
(let* ((frame ((%sym 'selected-frame)))
       (stored (stored-ie-after
                (lambda () (gen-help-event "help-f" frame #nil 'obj 5)))))
  (check "gen/frame-x" frame ((%sym '--ie-x) stored))
  (check "gen/frame-y" "help-f" ((%sym '--ie-y) stored)))

;;; --- 2. store-help-event: arg/x nil, timestamp 0 -------------------
(let* ((frame ((%sym 'selected-frame)))
       (stored (stored-ie-after
                (lambda () (store-help-event frame "help-s")))))
  (check "store/kind" HELP-EVENT ((%sym '--ie-kind) stored))
  (check "store/frame-or-window" frame ((%sym '--ie-frame-or-window) stored))
  (check "store/arg-nil" #nil ((%sym '--ie-arg) stored))
  (check "store/x-nil" #nil ((%sym '--ie-x) stored))
  (check "store/y" "help-s" ((%sym '--ie-y) stored))
  (check "store/timestamp-zero" 0 ((%sym '--ie-timestamp) stored)))

;;; --- 3. show-help-echo dispatch through the C entry point ----------
;;; --rc-show-help-echo (keyboard.c) calls show_help_echo, whose imp-3
;;; body dispatches into Scheme show-help-echo.  Batch is noninteractive,
;;; so the mouse-fixup block is skipped and the shared cell write is the
;;; observable effect.  Drive all three HELP shapes: string, function, nil.

;; 3a. string HELP through --rc-show-help-echo: shared cell set on.
(let ((saved-show (symbol-value 'show-help-function)))
  ((%sym '--rc-help-echo-showing-set!) #nil)
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ((%sym '--rc-show-help-echo) "hello" #nil #nil 0)
      (check "dispatch/string-cell-on" #t
             (truthy? ((%sym '--rc-help-echo-redisplay-preserve-p)))))
    (lambda () (set-symbol-value! 'show-help-function saved-show))))

;; 3b. function HELP through --rc-show-help-echo: show-help-function is
;; called with the substituted string, and the cell reflects the write.
(let ((saved-show (symbol-value 'show-help-function))
      (observed #nil))
  (set-symbol-value! 'show-help-function 'm16-obs-show)
  (set-symbol-function! 'm16-obs-show (lambda (h) (set! observed h)))
  (set-symbol-function! 'm16-help-fn (lambda (w o p) "from-fn"))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ((%sym '--rc-show-help-echo) 'm16-help-fn #nil #nil 0)
      (check "dispatch/function-called" #t
             (and (string? observed)
                  (not (eq? (string-contains observed "from-fn") #f))))
      (check "dispatch/function-cell-on" #t
             (truthy? ((%sym '--rc-help-echo-redisplay-preserve-p)))))
    (lambda () (set-symbol-value! 'show-help-function saved-show))))

;; 3c. nil HELP through --rc-show-help-echo: clears the cell.
(let ((saved-show (symbol-value 'show-help-function)))
  ((%sym '--rc-help-echo-showing-set!) #t)
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ((%sym '--rc-show-help-echo) #nil #nil #nil 0)
      (check "dispatch/nil-cell-off" #nil
             ((%sym '--rc-help-echo-redisplay-preserve-p))))
    (lambda () (set-symbol-value! 'show-help-function saved-show))))
