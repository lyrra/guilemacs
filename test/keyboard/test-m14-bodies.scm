;;; test-m14-bodies.scm --- M14 imp-2 test corpus for the 5 Scheme ring
;;; predicates & drainers in (emacs kbd-buffer):
;;; kbd-buffer-readable-events, kbd-buffer-process-special-events!,
;;; kbd-buffer-swallow-events!, kbd-buffer-discard-mouse-events!, and
;;; kbd-buffer-events-waiting.
;;;
;;; Sourced by test/keyboard/test-m14-bodies.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp — Scheme format output does not reach emacs --batch
;;; stdout.
;;;
;;; Seeding follows test-m14-shims.scm §6-7 / test-m13-store.scm:
;;; --ie-test-event + --kbd-set-fetch-ptr-index / --kbd-set-store-ptr-index
;;; + --kbd-store-buffered-event.  Every seeded sub-test runs inside a
;;; dynamic-wind that saves and restores the fetch/store cursors (and
;;; input-pending-p-filter-events / while-no-input-ignore-events for the
;;; phase-2 filter cases) — process-global state shared with every other
;;; test in the suite.  NO_EVENT slots are seeded with --ie-clear (a
;;; store-buffered-event of NO_EVENT would abort via kbd-buffer-store-event!'s
;;; NO_EVENT guard, test-m13-store.scm §10).
;;;
;;; The kind/flag constants are read from the module via @@ so the
;;; corpus uses the exact values the procedures compare against.

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

(define KBD-BUFFER-SIZE 4096)

;; Kind / flag constants — the authoritative values the procedures
;; compare against (KBD_BUFFER_SIZE is hardcoded here with a comment,
;; same as the module; no DEFUN exposes it).
(define NO-EVENT                (@@ (emacs kbd-buffer) NO-EVENT))
(define ASCII-KEYSTROKE-EVENT   (@@ (emacs kbd-buffer) ASCII-KEYSTROKE-EVENT))
(define FOCUS-IN-EVENT          (@@ (emacs kbd-buffer) FOCUS-IN-EVENT))
(define MOUSE-CLICK-EVENT       (@@ (emacs kbd-buffer) MOUSE-CLICK-EVENT))
(define SELECTION-REQUEST-EVENT (@@ (emacs kbd-buffer) SELECTION-REQUEST-EVENT))
(define READABLE-EVENTS-DO-TIMERS-NOW
  (@@ (emacs kbd-buffer) READABLE-EVENTS-DO-TIMERS-NOW))
(define FILTER-EVENTS           (@@ (emacs kbd-buffer) FILTER-EVENTS))
(define IGNORE-SQUEEZABLES      (@@ (emacs kbd-buffer) IGNORE-SQUEEZABLES))

;;; --- 0. Registration: the 10 imp-2 C shims resolve -------------------
;; Guards against a missing/renamed DEFUN (the C-helper-masquerading-as-
;; elisp trap, house rule).  The 3 pre-existing shims are from earlier
;; milestones, not new imp-1 work — they just were not imported before.
(for-each
 (lambda (n)
   (check (string-append "registered:" (symbol->string n))
          #t (not (eq? (%sym n) #nil))))
 '(--timer-check --toolkit-scroll-bars-p --kbd-queue-has-data
   --any-kbd-queue-has-data --kbd-excise-selection-event-at!
   --redisplay-preserve-echo-area --timers-run --get-input-pending
   --rc-input-pending --ie-part))

;;; --- 1. kbd-buffer-readable-events -----------------------------------

;; 1a. Empty ring, low flags: all 7 phases quiescent -> #nil.
(let* ((saved-fetch ((%sym '--kbd-fetch-ptr-index)))
       (saved-store ((%sym '--kbd-store-ptr-index))))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
      ((%sym '--kbd-set-store-ptr-index) saved-fetch)
      (check "readable/empty-low-flags" #nil
             (kbd-buffer-readable-events 0)))
    (lambda () ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
               ((%sym '--kbd-set-store-ptr-index) saved-store))))

;; 1b. Non-empty ring with flags = 0 -> #t immediately (no filter active).
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
      (check "readable/nonempty-flags-0" #t
             (kbd-buffer-readable-events 0)))
    (lambda () ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
               ((%sym '--kbd-set-store-ptr-index) saved-store))))

;; 1c. A focus-in event with FILTER_EVENTS set and
;; input-pending-p-filter-events nil is skipped; as the only event the
;; walk falls through to the quiescent tail -> #nil.
(let* ((saved-fetch ((%sym '--kbd-fetch-ptr-index)))
       (saved-store ((%sym '--kbd-store-ptr-index)))
       (saved-fev (symbol-value 'input-pending-p-filter-events))
       (saved-wni (symbol-value 'while-no-input-ignore-events))
       (base saved-fetch)
       (ie ((%sym '--ie-test-event) FOCUS-IN-EVENT 0 0 #nil)))
  (dynamic-wind
    (lambda () (set-symbol-value! 'input-pending-p-filter-events #nil)
               (set-symbol-value! 'while-no-input-ignore-events #nil))
    (lambda ()
      ((%sym '--kbd-set-fetch-ptr-index) base)
      ((%sym '--kbd-set-store-ptr-index) base)
      ((%sym '--kbd-store-buffered-event) ie #nil)
      (check "readable/focus-in-filter-var-nil" #nil
             (kbd-buffer-readable-events FILTER-EVENTS)))
    (lambda () ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
               ((%sym '--kbd-set-store-ptr-index) saved-store)
               (set-symbol-value! 'input-pending-p-filter-events saved-fev)
               (set-symbol-value! 'while-no-input-ignore-events saved-wni))))

;; 1d. Same focus-in event with input-pending-p-filter-events = t and an
;; empty ignore list: not ignored -> #t.
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
      (check "readable/focus-in-filter-var-t-not-ignored" #t
             (kbd-buffer-readable-events FILTER-EVENTS)))
    (lambda () ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
               ((%sym '--kbd-set-store-ptr-index) saved-store)
               (set-symbol-value! 'input-pending-p-filter-events saved-fev)
               (set-symbol-value! 'while-no-input-ignore-events saved-wni))))

;; 1e. Same focus-in event with input-pending-p-filter-events = t and a
;; `focus-in` entry in while-no-input-ignore-events: ignored -> #nil.
(let* ((saved-fetch ((%sym '--kbd-fetch-ptr-index)))
       (saved-store ((%sym '--kbd-store-ptr-index)))
       (saved-fev (symbol-value 'input-pending-p-filter-events))
       (saved-wni (symbol-value 'while-no-input-ignore-events))
       (base saved-fetch)
       (ie ((%sym '--ie-test-event) FOCUS-IN-EVENT 0 0 #nil)))
  (dynamic-wind
    (lambda () (set-symbol-value! 'input-pending-p-filter-events #t)
               (set-symbol-value! 'while-no-input-ignore-events
                                  (elist 'focus-in)))
    (lambda ()
      ((%sym '--kbd-set-fetch-ptr-index) base)
      ((%sym '--kbd-set-store-ptr-index) base)
      ((%sym '--kbd-store-buffered-event) ie #nil)
      (check "readable/focus-in-filter-var-t-ignored" #nil
             (kbd-buffer-readable-events FILTER-EVENTS)))
    (lambda () ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
               ((%sym '--kbd-set-store-ptr-index) saved-store)
               (set-symbol-value! 'input-pending-p-filter-events saved-fev)
               (set-symbol-value! 'while-no-input-ignore-events saved-wni))))

;;; --- 2. kbd-buffer-process-special-events! ---------------------------

;; 2a. One selection-request event at the fetch position: excised, ring
;; ends up empty (fetch advances onto store).
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
      (kbd-buffer-process-special-events!)
      (check "process-special/selection-ring-empty"
             ((%sym '--kbd-store-ptr-index))
             ((%sym '--kbd-fetch-ptr-index))))
    (lambda () ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
               ((%sym '--kbd-set-store-ptr-index) saved-store))))

;; 2b. A non-selection event is left untouched (fetch unmoved, kind kept).
(let* ((saved-fetch ((%sym '--kbd-fetch-ptr-index)))
       (saved-store ((%sym '--kbd-store-ptr-index)))
       (base saved-fetch)
       (ie ((%sym '--ie-test-event) ASCII-KEYSTROKE-EVENT 66 0 #nil)))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ((%sym '--kbd-set-fetch-ptr-index) base)
      ((%sym '--kbd-set-store-ptr-index) base)
      ((%sym '--kbd-store-buffered-event) ie #nil)
      (kbd-buffer-process-special-events!)
      (check "process-special/non-selection-fetch-unmoved" base
             ((%sym '--kbd-fetch-ptr-index)))
      (check "process-special/non-selection-kind-kept" ASCII-KEYSTROKE-EVENT
             ((%sym '--kbd-event-kind) base)))
    (lambda () ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
               ((%sym '--kbd-set-store-ptr-index) saved-store))))

;;; --- 3. kbd-buffer-swallow-events! smoke -----------------------------
;;; Empty ring, both do-display values: assert no error.  This milestone
;;; leaves timer_check a stub, so a real ripe-timer scenario is out of
;;; scope.
(let* ((saved-fetch ((%sym '--kbd-fetch-ptr-index)))
       (saved-store ((%sym '--kbd-store-ptr-index))))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
      ((%sym '--kbd-set-store-ptr-index) saved-fetch)
      (check "swallow/do-display-t" #t
             (no-error? (lambda () (kbd-buffer-swallow-events! #t))))
      (check "swallow/do-display-nil" #t
             (no-error? (lambda () (kbd-buffer-swallow-events! #nil)))))
    (lambda () ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
               ((%sym '--kbd-set-store-ptr-index) saved-store))))

;;; --- 4. kbd-buffer-discard-mouse-events! -----------------------------
;;; Seed one mouse-click-event and one ascii-keystroke: only the mouse
;;; event is blanked to NO_EVENT; the keystroke and the cursors stay.
;;; Each event is created-and-stored immediately (--ie-test-event reuses
;;; static storage, so two live handles would alias).
(let* ((saved-fetch ((%sym '--kbd-fetch-ptr-index)))
       (saved-store ((%sym '--kbd-store-ptr-index)))
       (base saved-fetch))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ((%sym '--kbd-set-fetch-ptr-index) base)
      ((%sym '--kbd-set-store-ptr-index) base)
      ((%sym '--kbd-store-buffered-event)
       ((%sym '--ie-test-event) MOUSE-CLICK-EVENT 0 0 #nil) #nil)
      ((%sym '--kbd-store-buffered-event)
       ((%sym '--ie-test-event) ASCII-KEYSTROKE-EVENT 67 0 #nil) #nil)
      (kbd-buffer-discard-mouse-events!)
      (check "discard-mouse/mouse-blanked" NO-EVENT
             ((%sym '--kbd-event-kind) base))
      (check "discard-mouse/keystroke-kept" ASCII-KEYSTROKE-EVENT
             ((%sym '--kbd-event-kind) (modulo (+ base 1) KBD-BUFFER-SIZE)))
      (check "discard-mouse/fetch-unmoved" base
             ((%sym '--kbd-fetch-ptr-index))))
    (lambda () ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
               ((%sym '--kbd-set-store-ptr-index) saved-store))))

;;; --- 5. kbd-buffer-events-waiting ------------------------------------
;;; The drainer keeps its side effect: it advances the fetch cursor.
;;; NO_EVENT slots are seeded by --ie-clear on the slot's ie-smob (a
;;; store-buffered-event of NO_EVENT would abort via
;;; kbd-buffer-store-event!'s NO_EVENT guard, test-m13-store.scm §10).

;; 5a. Leading NO_EVENT run followed by a real event: cursor advances
;; past the run and the return is #t.
(let* ((saved-fetch ((%sym '--kbd-fetch-ptr-index)))
       (saved-store ((%sym '--kbd-store-ptr-index)))
       (base saved-fetch))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ((%sym '--kbd-set-fetch-ptr-index) base)
      ((%sym '--kbd-set-store-ptr-index) (modulo (+ base 2) KBD-BUFFER-SIZE))
      ((%sym '--ie-clear) ((%sym '--kbd-event-ie) base))
      ((%sym '--ie-clear) ((%sym '--kbd-event-ie)
                           (modulo (+ base 1) KBD-BUFFER-SIZE)))
      ((%sym '--kbd-store-buffered-event)
       ((%sym '--ie-test-event) ASCII-KEYSTROKE-EVENT 68 0 #nil) #nil)
      (check "events-waiting/advance-past-run" #t
             (kbd-buffer-events-waiting))
      (check "events-waiting/fetch-advanced"
             (modulo (+ base 2) KBD-BUFFER-SIZE)
             ((%sym '--kbd-fetch-ptr-index))))
    (lambda () ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
               ((%sym '--kbd-set-store-ptr-index) saved-store))))

;; 5b. All-NO_EVENT ring: return is #nil (the documented type, matching
;; the elisp two-valued discipline) and the cursor lands on store.
(let* ((saved-fetch ((%sym '--kbd-fetch-ptr-index)))
       (saved-store ((%sym '--kbd-store-ptr-index)))
       (base saved-fetch)
       (store (modulo (+ base 2) KBD-BUFFER-SIZE)))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ((%sym '--kbd-set-fetch-ptr-index) base)
      ((%sym '--kbd-set-store-ptr-index) store)
      ((%sym '--ie-clear) ((%sym '--kbd-event-ie) base))
      ((%sym '--ie-clear) ((%sym '--kbd-event-ie)
                           (modulo (+ base 1) KBD-BUFFER-SIZE)))
      (check "events-waiting/all-no-event" #nil
             (kbd-buffer-events-waiting))
      (check "events-waiting/cursor-on-store" store
             ((%sym '--kbd-fetch-ptr-index))))
    (lambda () ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
               ((%sym '--kbd-set-store-ptr-index) saved-store))))
