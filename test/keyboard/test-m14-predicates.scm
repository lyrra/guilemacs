;;; test-m14-predicates.scm --- M14 imp-4 test corpus for the C->Scheme
;;; cutover of the 5 kbd-buffer predicates & drainers.
;;;
;;; M14 imp-2 (test-m14-bodies.scm) already exercises the 5 Scheme
;;; bodies in (emacs kbd-buffer) directly.  This corpus instead proves
;;; the cutover: that the C thin dispatchers (=readable_events=,
;;; =process_special_events=, =swallow_events=, =discard_mouse_events=,
;;; =kbd_buffer_events_waiting=) reach those Scheme bodies.  It drives
;;; the three C functions that expose an elisp-visible DEFUN shim and
;;; observes the observable behavior (return value, fetch/store
;;; cursors) that only the Scheme body produces:
;;;
;;;   --get-input-pending FLAGS -> get_input_pending -> readable_events
;;;   --process-special-events  -> process_special_events
;;;   --rc-swallow-events       -> swallow_events (false)
;;;
;;; =discard_mouse_events= and =kbd_buffer_events_waiting= have no
;;; elisp shim (their only callers are =term.c=/=msdos.c=, unchanged).
;;; Their cutover is exercised by test-m14-bodies.scm on the Scheme
;;; bodies and by inspection of the trivial one-line dispatchers.
;;;
;;; Sourced by test/keyboard/test-m14-predicates.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp — Scheme format output does not reach emacs --batch
;;; stdout.
;;;
;;; Seeding follows test-m14-bodies.scm: --ie-test-event +
;;; --kbd-set-fetch-ptr-index / --kbd-set-store-ptr-index +
;;; --kbd-store-buffered-event.  Every sub-test runs inside a
;;; dynamic-wind that saves and restores the fetch/store cursors (and
;;; the phase-2 filter vars for the FILTER_EVENTS cases).
;;;
;;; FLAGS bit values (src/keyboard.c :375-377): 1=DO_TIMERS_NOW,
;;; 2=FILTER_EVENTS, 4=IGNORE_SQUEEZABLES.

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

(define (elist . items)
  (let loop ((i items))
    (if (null? i) #nil (cons (car i) (loop (cdr i))))))

(define (no-error? thunk)
  (catch #t
    (lambda () (thunk) #t)
    (lambda (key . args) (list 'error key args))))

(define KBD-BUFFER-SIZE 4096)

(define NO-EVENT                (@@ (emacs kbd-buffer) NO-EVENT))
(define ASCII-KEYSTROKE-EVENT   (@@ (emacs kbd-buffer) ASCII-KEYSTROKE-EVENT))
(define FOCUS-IN-EVENT          (@@ (emacs kbd-buffer) FOCUS-IN-EVENT))
(define SELECTION-REQUEST-EVENT (@@ (emacs kbd-buffer) SELECTION-REQUEST-EVENT))

(define FLAG-FILTER-EVENTS 2)

;;; --- 0. Registration: the 3 elisp-visible cutover shims resolve ------
;; Guards against a renamed/missing DEFUN (the
;; C-helper-masquerading-as-elisp trap, house rule).
(for-each
 (lambda (n)
   (check (string-append "registered:" (symbol->string n))
          #t (not (eq? (%sym n) #nil))))
 '(--get-input-pending --process-special-events --rc-swallow-events))

;;; --- 1. readable_events cutover via --get-input-pending --------------

;; 1a. Empty ring, mask 0 -> nil (Scheme body reports nothing readable).
;; quit-flag is cleared first: --get-input-pending ORs Vquit_flag into
;; its result (keyboard.c:8121), so a leaked quit-flag from an earlier
;; test in the suite would spuriously turn this into t.
(let* ((saved-fetch ((%sym '--kbd-fetch-ptr-index)))
       (saved-store ((%sym '--kbd-store-ptr-index)))
       (saved-qf (symbol-value 'quit-flag)))
  (dynamic-wind
    (lambda () (set-symbol-value! 'quit-flag #nil))
    (lambda ()
      ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
      ((%sym '--kbd-set-store-ptr-index) saved-fetch)
      (check "cutover/gip-empty-mask0" #nil
             ((%sym '--get-input-pending) 0)))
    (lambda () ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
               ((%sym '--kbd-set-store-ptr-index) saved-store)
               (set-symbol-value! 'quit-flag saved-qf))))

;; 1b. Seeded keystroke, mask 0 -> t (the event reaches the Scheme
;; readable-events walk through the C dispatcher).
(let* ((saved-fetch ((%sym '--kbd-fetch-ptr-index)))
       (saved-store ((%sym '--kbd-store-ptr-index)))
       (base saved-fetch)
       (ie ((%sym '--ie-test-event) ASCII-KEYSTROKE-EVENT 65 0 #nil)))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ((%sym '--kbd-set-fetch-ptr-index) base)
      ((%sym '--kbd-set-store-ptr-index) base)
      ((%sym '--kbd-store-buffered-event) ie #nil)
      (check "cutover/gip-seeded-keystroke-t" #t
             ((%sym '--get-input-pending) 0)))
    (lambda () ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
               ((%sym '--kbd-set-store-ptr-index) saved-store))))

;; 1c. Seeded focus-in with FILTER_EVENTS(2) and
;; input-pending-p-filter-events nil: filtered -> nil.  Proves the flag
;; bit is carried from C into the Scheme filter.
(let* ((saved-fetch ((%sym '--kbd-fetch-ptr-index)))
       (saved-store ((%sym '--kbd-store-ptr-index)))
       (saved-fev (symbol-value 'input-pending-p-filter-events))
       (saved-wni (symbol-value 'while-no-input-ignore-events))
       (saved-qf (symbol-value 'quit-flag))
       (base saved-fetch)
       (ie ((%sym '--ie-test-event) FOCUS-IN-EVENT 0 0 #nil)))
  (dynamic-wind
    (lambda () (set-symbol-value! 'input-pending-p-filter-events #nil)
               (set-symbol-value! 'while-no-input-ignore-events #nil)
               (set-symbol-value! 'quit-flag #nil))
    (lambda ()
      ((%sym '--kbd-set-fetch-ptr-index) base)
      ((%sym '--kbd-set-store-ptr-index) base)
      ((%sym '--kbd-store-buffered-event) ie #nil)
      (check "cutover/gip-focus-in-filter-var-nil" #nil
             ((%sym '--get-input-pending) FLAG-FILTER-EVENTS)))
    (lambda () ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
               ((%sym '--kbd-set-store-ptr-index) saved-store)
               (set-symbol-value! 'input-pending-p-filter-events saved-fev)
               (set-symbol-value! 'while-no-input-ignore-events saved-wni)
               (set-symbol-value! 'quit-flag saved-qf))))

;; 1d. Same focus-in with filter var t: not ignored -> t.
(let* ((saved-fetch ((%sym '--kbd-fetch-ptr-index)))
       (saved-store ((%sym '--kbd-store-ptr-index)))
       (saved-fev (symbol-value 'input-pending-p-filter-events))
       (saved-wni (symbol-value 'while-no-input-ignore-events))
       (base saved-fetch)
       (ie ((%sym '--ie-test-event) FOCUS-IN-EVENT 0 0 #nil)))
  (dynamic-wind
    (lambda () (set-symbol-value! 'input-pending-p-filter-events #t)
               (set-symbol-value! 'while-no-input-ignore-events #nil))
    (lambda ()
      ((%sym '--kbd-set-fetch-ptr-index) base)
      ((%sym '--kbd-set-store-ptr-index) base)
      ((%sym '--kbd-store-buffered-event) ie #nil)
      (check "cutover/gip-focus-in-filter-var-t" #t
             ((%sym '--get-input-pending) FLAG-FILTER-EVENTS)))
    (lambda () ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
               ((%sym '--kbd-set-store-ptr-index) saved-store)
               (set-symbol-value! 'input-pending-p-filter-events saved-fev)
               (set-symbol-value! 'while-no-input-ignore-events saved-wni))))

;; 1e. Same focus-in with filter var t and a `focus-in' entry in
;; while-no-input-ignore-events: ignored -> nil.
(let* ((saved-fetch ((%sym '--kbd-fetch-ptr-index)))
       (saved-store ((%sym '--kbd-store-ptr-index)))
       (saved-fev (symbol-value 'input-pending-p-filter-events))
       (saved-wni (symbol-value 'while-no-input-ignore-events))
       (saved-qf (symbol-value 'quit-flag))
       (base saved-fetch)
       (ie ((%sym '--ie-test-event) FOCUS-IN-EVENT 0 0 #nil)))
  (dynamic-wind
    (lambda () (set-symbol-value! 'input-pending-p-filter-events #t)
               (set-symbol-value! 'while-no-input-ignore-events
                                  (elist 'focus-in))
               (set-symbol-value! 'quit-flag #nil))
    (lambda ()
      ((%sym '--kbd-set-fetch-ptr-index) base)
      ((%sym '--kbd-set-store-ptr-index) base)
      ((%sym '--kbd-store-buffered-event) ie #nil)
      (check "cutover/gip-focus-in-filter-var-t-ignored" #nil
             ((%sym '--get-input-pending) FLAG-FILTER-EVENTS)))
    (lambda () ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
               ((%sym '--kbd-set-store-ptr-index) saved-store)
               (set-symbol-value! 'input-pending-p-filter-events saved-fev)
               (set-symbol-value! 'while-no-input-ignore-events saved-wni)
               (set-symbol-value! 'quit-flag saved-qf))))

;;; --- 2. process_special_events cutover via --process-special-events --
;;; A seeded selection-request event at the fetch position is excised
;;; (fetch advances onto store, ring empty).  Proves the C shim reaches
;;; the Scheme process-special-events! body.
(let* ((saved-fetch ((%sym '--kbd-fetch-ptr-index)))
       (saved-store ((%sym '--kbd-store-ptr-index)))
       (base saved-fetch)
       (ie ((%sym '--ie-test-event) SELECTION-REQUEST-EVENT 0 0 #nil)))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ((%sym '--kbd-set-fetch-ptr-index) base)
      ((%sym '--kbd-set-store-ptr-index) base)
      ((%sym '--kbd-store-buffered-event) ie #nil)
      ((%sym '--process-special-events))
      (check "cutover/process-special/selection-ring-empty"
             ((%sym '--kbd-store-ptr-index))
             ((%sym '--kbd-fetch-ptr-index))))
    (lambda () ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
               ((%sym '--kbd-set-store-ptr-index) saved-store))))

;;; --- 3. swallow_events cutover via --rc-swallow-events ---------------
;;; --rc-swallow-events calls swallow_events (false), which must run the
;;; Scheme kbd-buffer-swallow-events! without error on an empty ring
;;; (the do-display=false branch).
(let* ((saved-fetch ((%sym '--kbd-fetch-ptr-index)))
       (saved-store ((%sym '--kbd-store-ptr-index))))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
      ((%sym '--kbd-set-store-ptr-index) saved-fetch)
      (check "cutover/rc-swallow-no-error" #t
             (no-error? (lambda () ((%sym '--rc-swallow-events))))))
    (lambda () ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
               ((%sym '--kbd-set-store-ptr-index) saved-store))))
