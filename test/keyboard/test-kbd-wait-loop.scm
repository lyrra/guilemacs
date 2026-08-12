;;; test-kbd-wait-loop.scm --- M11 imp-2 test corpus for (emacs kbd-buffer)
;;;
;;; Sourced by test/keyboard/test-kbd-wait-loop.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp — Scheme format output does not reach emacs --batch
;;; stdout.
;;;
;;; No-blocking cases only; everything sleeping is deferred to imp-6
;;; and the smoke gate:
;;;   1. Module registration: kbd-buffer-get-event / noninteractive-fast-path?
;;;   2. Gate predicate: t in batch, daemon composition consistent
;;;   3. Vunread break + drain (proves the loop's first check runs)
;;;   4. Fast path in batch (shape-adaptive — see the #nil trap below)
;;;   5. End-time expiry: timed branch's expired arm + entry-sync
;;;   6. Queue exit: --kbd-buffer-store-fake-event → dispatch seam throw
;;;   7. --rc-end-time-remaining shape
;;;
;;; The batch fast-path trap: this build is compiled with HAVE_DBUS /
;;; USE_FILE_NOTIFY, so --kbd-noninteractive-getchar returns nil (the C
;;; compiles the whole fast-path block out) and kbd-buffer-get-event
;;; falls through to the wait loop.  On fast-path builds getchar() runs
;;; instead (stdin EOF in CI ⇒ -1).  Tests 3/5/6 bind the elisp
;;; `noninteractive` variable to nil so the wait loop is reached on
;;; every build.

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

;;; --- Helpers ----------------------------------------------------------

;; Run THUNK with the elisp `noninteractive` variable bound to nil, so
;; the wait loop is reached even in batch.  Same save/restore idiom as
;; command-loop.scm's inhibit-quit dance: set-symbol-value! is the
;; C-backed one at runtime and writes the DEFVAR_BOOL through.
(define (with-noninteractive-nil thunk)
  (let ((saved (symbol-value 'noninteractive)))
    (dynamic-wind
      (lambda () (set-symbol-value! 'noninteractive #nil))
      thunk
      (lambda () (set-symbol-value! 'noninteractive saved)))))

;; Push a fresh <rc-state> rec (with optional FIELD→VALUE settings)
;; for the duration of THUNK, so the rec-based write-back DEFUNs
;; (--rc-write-kbp / --rc-end-time-expired-p / --rc-end-time-remaining)
;; see rc_state_depth > 0.
(define (with-rc-rec field-vals thunk)
  (let* ((rec ((%sym '--make-rc-state)))
         (set-f (%sym '--rc-test-state-set!)))
    (for-each (lambda (fv)
                (set-f rec (car fv) (cdr fv)))
              field-vals)
    ((%sym '--rc-record-stack-push) rec)
    (dynamic-wind
      (lambda () #f)
      thunk
      (lambda () ((%sym '--rc-record-stack-pop))))))

;;; --- 1. Registration --------------------------------------------------

(check "registration/kbd-buffer-get-event" #t
       (procedure? kbd-buffer-get-event))
(check "registration/noninteractive-fast-path?" #t
       (procedure? noninteractive-fast-path?))

;;; --- 2. Gate predicate ------------------------------------------------

;; In batch, noninteractive is t → the gate is t.
(check "gate/batch" #t (noninteractive-fast-path?))

;; Daemon composition: batch has no daemon, so --daemon-not-yet-running-p
;; is nil and daemonp is nil; the elisp `and` (daemonp) (not
;; --daemon-not-yet-running-p) is nil.  #nil is a distinct object in
;; this runtime (≠ () and ≠ #f), so the composition must be evaluated
;; with explicit elisp truthiness, not Scheme and/not.
(let ((dn ((%sym '--daemon-not-yet-running-p)))
      (dp ((%sym 'daemonp))))
  (check "gate/daemon-not-yet-shape" #nil dn)
  (check "gate/daemonp-shape" #nil dp)
  (check "gate/daemon-composition" #nil
         (if (eq? dp #nil) #nil
             (if (eq? dn #nil) #t #nil))))

;; Daemon composition arm exercised through the predicate itself (the
;; existing gate/daemon-composition check above re-derives the boolean
;; inline rather than calling noninteractive-fast-path?).  Stub both
;; DEFUNs to elisp t — the daemon-not-yet-detached case (IS_DAEMON &&
;; !DAEMON_RUNNING): C says the fast path is false, so the predicate
;; must return #f.  The delayed DEFUN refs are private module state, so
;; rebind them directly and restore them afterwards; the pre-fix gate
;; returned t here because Scheme `not`/`and`/`or` treat #f and #nil as
;; distinct objects.
(let ((saved-dp (@@ (emacs kbd-buffer) %daemonp))
      (saved-dn (@@ (emacs kbd-buffer) %--daemon-not-yet-running-p)))
  (dynamic-wind
    (lambda ()
      (set! (@@ (emacs kbd-buffer) %daemonp) (delay (lambda () #t)))
      (set! (@@ (emacs kbd-buffer) %--daemon-not-yet-running-p)
            (delay (lambda () #t))))
    (lambda ()
      (with-noninteractive-nil
        (lambda ()
          (check "gate/daemon-arm-not-running" #f
                 (noninteractive-fast-path?)))))
    (lambda ()
      (set! (@@ (emacs kbd-buffer) %daemonp) saved-dp)
      (set! (@@ (emacs kbd-buffer) %--daemon-not-yet-running-p) saved-dn))))

;;; --- 3. Vunread break + drain -----------------------------------------

;; Push a rec (kbp write-back needs rc depth > 0), set
;; unread-command-events, call the proc with the wait loop reached
;; (noninteractive bound to nil).  The loop's first check breaks on the
;; Vunread list; the drain pops it, writes back *kbp, and returns the
;; raw car (no (Qt . e) / (Qno_record . e) peeling — that is M8i's job
;; in read-char.scm).
(let ((kb ((%sym 'current-kboard))))
  (with-rc-rec `((kbp . ,((%sym '--rc-test-kbp-storage-ptr))))
    (lambda ()
      (with-noninteractive-nil
        (lambda ()
          (set-symbol-value! 'unread-command-events (cons 'x #nil))
          (let ((r (kbd-buffer-get-event #nil #nil #nil)))
            (check "vunread/returns-first" 'x r)
            (check "vunread/drained" #nil (symbol-value 'unread-command-events))
            (check "vunread/kbp-written" #t
                   (not (eq? ((%sym 'kboard-eq)
                              ((%sym '--rc-test-kbp-storage-value)) kb)
                             #nil)))))))))

;; kbp entry-sync: rec with a nil kbp slot, pointer passed as the 1st
;; arg — entry-sync copies it in, so the write-back still lands.
(let ((kb ((%sym 'current-kboard))))
  (with-rc-rec '()
    (lambda ()
      (with-noninteractive-nil
        (lambda ()
          (set-symbol-value! 'unread-command-events (cons 'z #nil))
          (check "vunread/entry-sync-returns" 'z
                 (kbd-buffer-get-event ((%sym '--rc-test-kbp-storage-ptr))
                                       #nil #nil))
          (check "vunread/entry-sync-kbp-written" #t
                 (not (eq? ((%sym 'kboard-eq)
                            ((%sym '--rc-test-kbp-storage-value)) kb)
                           #nil))))))))

;;; --- 4. Fast path in batch --------------------------------------------

;; Batch (noninteractive t, stdin EOF in CI).  Shape-adaptive because
;; of the #nil trap: on builds WITH the fast path,
;; --kbd-noninteractive-getchar returns a fixnum (EOF ⇒ -1) and the
;; proc returns exactly that without blocking, writing back *kbp.  On
;; builds compiled with DBus / file-notify / threads (like this one)
;; the DEFUN returns nil and the proc must NOT return that nil as an
;; event — it falls through to the wait loop, observable via a Vunread
;; break.
(let* ((kb ((%sym 'current-kboard)))
       (c ((%sym '--kbd-noninteractive-getchar))))
  (if (eq? c #nil)
      (with-rc-rec `((kbp . ,((%sym '--rc-test-kbp-storage-ptr))))
        (lambda ()
          (set-symbol-value! 'unread-command-events (cons 'y #nil))
          (check "fast-path/no-fast-path/falls-through" 'y
                 (kbd-buffer-get-event #nil #nil #nil))
          (check "fast-path/no-fast-path/kbp-written" #t
                 (not (eq? ((%sym 'kboard-eq)
                            ((%sym '--rc-test-kbp-storage-value)) kb)
                           #nil)))))
      (with-rc-rec `((kbp . ,((%sym '--rc-test-kbp-storage-ptr))))
        (lambda ()
          (check "fast-path/returns-getchar" c
                 (kbd-buffer-get-event #nil #nil #nil))
          (check "fast-path/kbp-written" #t
                 (not (eq? ((%sym 'kboard-eq)
                            ((%sym '--rc-test-kbp-storage-value)) kb)
                           #nil)))))))

;;; --- 5. End-time expiry (timed branch, expired arm) -------------------

;; With the rec's end-time slot holding the expired pointer and the
;; same pointer passed as the 3rd arg, the timed branch sees the
;; expired deadline and returns nil immediately (no sleep).  Two
;; forms: (a) slot pre-set, (b) slot nil with the pointer passed as
;; the arg — entry-sync copies it into the slot, which is what makes
;; --rc-end-time-expired-p see it.
(let ((expired-ptr ((%sym '--rc-test-expired-end-time-ptr))))
  (with-rc-rec `((end-time . ,expired-ptr))
    (lambda ()
      (with-noninteractive-nil
        (lambda ()
          (check "end-time-expiry/slot-set" #nil
                 (kbd-buffer-get-event #nil #nil expired-ptr))))))
  (with-rc-rec '()
    (lambda ()
      (with-noninteractive-nil
        (lambda ()
          (check "end-time-expiry/entry-sync" #nil
                 (kbd-buffer-get-event #nil #nil expired-ptr)))))))

;;; --- 6. Queue exit → dispatch seam ------------------------------------

;; Stuff one event via --kbd-buffer-store-fake-event (imp-1.4, pulled
;; forward into imp-2 prep), then the loop breaks on fetch ≠ store at
;; the first check and reaches the imp-3 dispatch seam, which throws
;; not-implemented.  The event is NOT dequeued (dequeue is imp-3's
;; job), so fetch ≠ store still holds after the throw.
(with-noninteractive-nil
  (lambda ()
    (set-symbol-value! 'unread-command-events #nil)
    ;; ASCII_KEYSTROKE_EVENT = 1 (enum event_kind, src/termhooks.h —
    ;; stable, precedes the #ifdef'd entries).
    ((%sym '--kbd-buffer-store-fake-event) 1 'fake-arg)
    (check "queue-exit/queue-nonempty" #t
           (not (= ((%sym '--kbd-fetch-ptr-index))
                   ((%sym '--kbd-store-ptr-index)))))
    (let ((r (catch 'not-implemented
               (lambda () (kbd-buffer-get-event #nil #nil #nil))
               (lambda (k . args) (cons k args)))))
      (check "queue-exit/dispatch-seam-throws" 'not-implemented (car r))
      (check "queue-exit/dispatch-seam-message" "imp-3/imp-4"
             (if (pair? (cdr r)) (cadr r) #nil)))
    (check "queue-exit/event-not-dequeued" #t
           (not (= ((%sym '--kbd-fetch-ptr-index))
                   ((%sym '--kbd-store-ptr-index)))))))

;;; --- 7. --rc-end-time-remaining shape ---------------------------------

;; nil at rc depth 0 (no rec).
(check "end-time-remaining/no-rec" #nil ((%sym '--rc-end-time-remaining)))

;; nil with a rec but no end-time slot.
(with-rc-rec '()
  (lambda ()
    (check "end-time-remaining/rec-no-end-time" #nil
           ((%sym '--rc-end-time-remaining)))))

;; (SEC . NSEC) fixnums with SEC ≥ 0 when an unexpired static timespec
;; is stored (far-future pointer).  Do NOT call kbd-buffer-get-event
;; with this pointer — the untimed wait would sleep until year 2038.
(with-rc-rec `((end-time . ,((%sym '--rc-test-far-future-end-time-ptr))))
  (lambda ()
    (let ((r ((%sym '--rc-end-time-remaining))))
      (check "end-time-remaining/far-future-cons" #t (pair? r))
      (check "end-time-remaining/sec-fixnum" #t
             (and (integer? (car r)) (>= (car r) 0)))
      (check "end-time-remaining/nsec-fixnum" #t
             (and (integer? (cdr r)) (>= (cdr r) 0))))))
