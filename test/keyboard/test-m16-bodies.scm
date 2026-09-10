;;; test-m16-bodies.scm --- M16 imp-2 test corpus for the 3 Scheme
;;; help-echo procedures in (emacs help-echo): show-help-echo,
;;; gen-help-event, and store-help-event.
;;;
;;; Sourced by test/keyboard/test-m16-bodies.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp.  See docs/m16-plan.org §imp-2 and brief.org.
;;;
;;; gen-help-event / store-help-event store into the real M13 ring via
;;; kbd-buffer-store-event!; the stored copy is read back with the ie
;;; accessors (same idiom as test-m16-shims.scm).  Every sub-test that
;;; advances the store pointer or mutates shared state (store-ptr,
;;; showing cell, track-mouse, noninteractive, show-help-function, the
;;; mouse-fixup binding) runs inside a dynamic-wind that restores it.

(use-modules (emacs help-echo))
(use-modules (emacs lispy-position))

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

;; HELP_EVENT kind constant — derived via (emacs lispy-position)
;; ie-kind-from-name so the test uses the exact enum value, not a copy
;; (same as test-m16-shims.scm).
(define HELP-EVENT (ie-kind-from-name 'help-echo))

;;; --- 0. Registration: the module's 3 procedures + shims resolve ---
(for-each
 (lambda (n)
   (check (string-append "proc:" (symbol->string n))
          #t (procedure? (module-ref (resolve-module '(emacs help-echo)) n))))
 '(show-help-echo gen-help-event store-help-event))
(for-each
 (lambda (n)
   (check (string-append "registered:" (symbol->string n))
          #t (not (eq? (%sym n) #nil))))
 '(--ie-help-event --position-to-time --safe-calln-or-eval
   --rc-help-echo-showing-set! --frame-set-mouse-moved! --some-mouse-moved
   --ie-kind --ie-frame-or-window --ie-arg --ie-x --ie-y --ie-timestamp
   --kbd-event-ie --kbd-store-ptr-index --kbd-set-store-ptr-index))

;;; --- 1. gen-help-event: field mapping ------------------------------
;;; Window case: x = WINDOW.  Frame-fallback case: x = FRAME.

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

;;; --- 3. show-help-echo: string HELP passes through substitute ------
;;; A string HELP (noninteractive t in batch, so the mouse-fixup block
;;; is skipped) reaches show-help-function with the substituted text,
;;; and the shared cell reflects the write.

;; 3a. string HELP without show-help-function: only the shared cell.
(let ((saved-show (symbol-value 'show-help-function))
      (saved-track (symbol-value 'track-mouse)))
  ((%sym '--rc-help-echo-showing-set!) #nil)
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      (show-help-echo "hello" #nil #nil 0)
      (check "show/string-cell-on" #t
             (truthy? ((%sym '--rc-help-echo-redisplay-preserve-p)))))
    (lambda ()
      (set-symbol-value! 'show-help-function saved-show)
      (set-symbol-value! 'track-mouse saved-track))))

;; 3b. string HELP with show-help-function bound: it is called with the
;; substituted string (the literal text survives substitute-command-keys).
(let ((saved-show (symbol-value 'show-help-function))
      (observed #nil))
  (set-symbol-value! 'show-help-function 'm16-obs-show)
  (set-symbol-function! 'm16-obs-show (lambda (h) (set! observed h)))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      (show-help-echo "passes-thru" #nil #nil 0)
      (check "show/string-substituted-string" #t (string? observed))
      (check "show/string-substituted-contains"
             #t (and (string? observed)
                     (not (eq? (string-contains observed "passes-thru") #f)))))
    (lambda () (set-symbol-value! 'show-help-function saved-show))))

;;; --- 4. show-help-echo: non-string HELP resolves through the shim --
;;; Both the function branch and the form branch of --safe-calln-or-eval,
;;; plus the early-stop path (resolved to a non-string).

;; 4a. function branch: a function HELP returns a string.
(let ((saved-show (symbol-value 'show-help-function))
      (observed #nil))
  (set-symbol-value! 'show-help-function 'm16-obs-show)
  (set-symbol-function! 'm16-obs-show (lambda (h) (set! observed h)))
  (set-symbol-function! 'm16-help-fn (lambda (w o p) "from-fn"))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      (show-help-echo 'm16-help-fn #nil #nil 0)
      (check "show/nonstring-function-called" #t
             (and (string? observed)
                  (not (eq? (string-contains observed "from-fn") #f)))))
    (lambda () (set-symbol-value! 'show-help-function saved-show))))

;; 4b. form branch: a non-function, non-string HELP (a variable symbol
;; holding a string) evaluates to a string.
(let ((saved-show (symbol-value 'show-help-function))
      (observed #nil))
  (set-symbol-value! 'show-help-function 'm16-obs-show)
  (set-symbol-function! 'm16-obs-show (lambda (h) (set! observed h)))
  (set-symbol-value! 'm16-form-var "form-result")
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      (show-help-echo 'm16-form-var #nil #nil 0)
      (check "show/nonstring-form-called" #t
             (and (string? observed)
                  (not (eq? (string-contains observed "form-result") #f)))))
    (lambda () (set-symbol-value! 'show-help-function saved-show))))

;; 4c. early stop: HELP resolves to a non-string — show-help-function is
;; never called and the shared cell stays off (C bare return).
(let ((saved-show (symbol-value 'show-help-function))
      (called #nil))
  (set-symbol-value! 'show-help-function 'm16-obs-show)
  (set-symbol-function! 'm16-obs-show (lambda (h) (set! called #t)))
  (set-symbol-function! 'm16-err-fn (lambda (w o p) 42))
  ((%sym '--rc-help-echo-showing-set!) #nil)
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      (show-help-echo 'm16-err-fn #nil #nil 0)
      (check "show/nonstring-nonstring-not-called" #nil called)
      (check "show/nonstring-nonstring-cell-off" #nil
             ((%sym '--rc-help-echo-redisplay-preserve-p))))
    (lambda () (set-symbol-value! 'show-help-function saved-show))))

;;; --- 5. show-help-echo: mouse_moved save/restore block ------------
;;; With noninteractive nil the mouse-fixup block runs.  Batch cannot
;;; arrange track_mouse observation reliably (test-m16-shims.scm note),
;;; so we verify the block executes: mouse-fixup-help-message is called
;;; and the whole call does not signal.  Track-mouse/noninteractive are
;;; set so the block would observe a frame were one available.
(let ((saved-ni (symbol-value 'noninteractive))
      (saved-track (symbol-value 'track-mouse))
      (saved-show (symbol-value 'show-help-function))
      (fixed-up #nil))
  (set-symbol-value! 'noninteractive #nil)
  (set-symbol-value! 'track-mouse #t)
  (set-symbol-value! 'show-help-function #nil)
  (set-symbol-function! 'mouse-fixup-help-message
                        (lambda (h) (set! fixed-up #t) h))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      (check "show/mousefixup-block-no-signal" #t
             (no-error? (lambda () (show-help-echo "hello" #nil #nil 0))))
      (check "show/mousefixup-block-called" #t fixed-up))
    (lambda ()
      (set-symbol-value! 'noninteractive saved-ni)
      (set-symbol-value! 'track-mouse saved-track)
      (set-symbol-value! 'show-help-function saved-show))))
