;;; test-m17-record-char.scm --- M17 imp-3 test corpus for the C-to-Scheme
;;; cutover of record_char and the --record-recent-keys-cmd-pseudo-event
;;; writer.
;;;
;;; Sourced by test/keyboard/test-m17-record-char.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp.  See docs/m17-plan.org §imp-3 and brief.org.
;;;
;;; imp-3 turns record_char and --record-recent-keys-cmd-pseudo-event into
;;; thin dispatchers into (emacs recent-keys): record-char and the new
;;; record-cmd-pseudo-event!, which reuses record-char-write-back's append
;;; logic so the recent-keys ring has one writer, not two.  This corpus
;;; drives the REAL C entry point --record-recent-keys-cmd-pseudo-event
;;; and the (emacs recent-keys) record-char port directly — M28 imp-5
;;; (family 1, group 2) removed the --rc-record-char double-hop, as
;;; record_char is now a thin dispatcher into the port.  This proves the
;;; C-to-Scheme wiring, exactly like test-m16-help-echo.scm does for its
;;; cutover.
;;;
;;; Every sub-test that mutates the ring or the guarded elisp vars
;;; (record-all-keys, inhibit--record-char, executing-kbd-macro,
;;; num-nonmacro-input-events) runs inside a with-ring-state dynamic-wind
;;; that resets the ring and restores the vars (same discipline as
;;; test-m17-bodies.scm).

(use-modules (emacs recent-keys))
(use-modules (emacs-elisp runtime))

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

;;; Build an elisp list (terminated by #nil), so it compares equal to a
;;; value read back from an elisp vector slot.
(define (elist . items)
  (let loop ((i items))
    (if (null? i) #nil (cons (car i) (loop (cdr i))))))

;;; --- Ring access helpers (same shape as test-m17-bodies.scm) ---------
;;; recent_keys is an elisp vector, not a Guile vector: read/write it via
;;; the C aref/aset, never vector-ref/vector-set!.
(define (ring)        ((%sym '--recent-keys-ring)))
(define (ridx)        ((%sym '--recent-keys-index)))
(define (rtotal)      ((%sym '--total-keys)))
(define (rlimit)      ((%sym '--lossage-limit)))
(define (rref i)      ((%sym 'aref) (ring) i))
(define (reset-ring!) ((%sym '--clear-recent-keys-ring)))
(define (set-idx! n)  ((%sym '--recent-keys-index-set!) n))
(define (set-total! n) ((%sym '--total-keys-set!) n))

;;; Event constructor.  A help-echo event's help string is its caddr
;;; (C: help = Fcar_safe (Fcdr_safe (XCDR (c)))).
(define (help-event tip) (list 'help-echo 'win tip 'other))

;;; Run THUNK with a fresh ring, a non-inhibited recording state, and
;;; restore all guarded elisp vars + counter afterwards.
(define (with-ring-state thunk)
  (let ((saved-counter (symbol-value 'num-nonmacro-input-events))
        (saved-rak     (symbol-value 'record-all-keys))
        (saved-irr     (symbol-value 'inhibit--record-char))
        (saved-ekm     (symbol-value 'executing-kbd-macro)))
    (dynamic-wind
      (lambda ()
        (reset-ring!)
        (set-symbol-value! 'record-all-keys #t)
        (set-symbol-value! 'inhibit--record-char #nil)
        (set-symbol-value! 'executing-kbd-macro #nil))
      thunk
      (lambda ()
        (reset-ring!)
        (set-symbol-value! 'num-nonmacro-input-events saved-counter)
        (set-symbol-value! 'record-all-keys saved-rak)
        (set-symbol-value! 'inhibit--record-char saved-irr)
        (set-symbol-value! 'executing-kbd-macro saved-ekm)))))

;;; --- 0. Registration: both Scheme targets resolve from (emacs recent-keys)
;;; The C dispatchers fill a static SCM cache via scm_c_public_ref, so a
;;; failed resolve would surface as an unbound-variable error at first call,
;;; not here.  This section just confirms the procedures exist as expected.
(define m17-mod (resolve-module '(emacs recent-keys)))
(check "record-char/resolves" #t (procedure? (module-ref m17-mod 'record-char)))
(check "record-cmd-pseudo-event!/resolves" #t
       (procedure? (module-ref m17-mod 'record-cmd-pseudo-event!)))
;; The C entry point this corpus drives must resolve as an elisp function.
(check "rc-record-char-retired" #t (eq? (%sym '--rc-record-char) #nil))
(check "pseudo-event-entry" #t
       (not (eq? (%sym '--record-recent-keys-cmd-pseudo-event) #nil)))

;;; --- 1. record-char port: plain-key append ---------------------------
;;; Drives the (emacs recent-keys) record-char port directly.
(with-ring-state
 (lambda ()
   (set-idx! 2) (set-total! 2)
   ((%sym 'aset) (ring) 0 97)
   ((%sym 'aset) (ring) 1 98)
   (let ((c0 (symbol-value 'num-nonmacro-input-events)))
     (record-char 99)
     (check "dispatch/plain-ring-slot" 99 (rref 2))
     (check "dispatch/plain-index-advance" 3 (ridx))
     (check "dispatch/plain-total-incr" 3 (rtotal))
     (check "dispatch/plain-counter-incr" (+ c0 1)
            (symbol-value 'num-nonmacro-input-events)))))

;;; --- 2. record-char port: help-echo dedup leaves the ring unchanged ---
;;; Repeated help-echo -> recorded = 1: no ring write, index/total stay put.
(with-ring-state
 (lambda ()
   (set-idx! 1) (set-total! 1)
   (let ((tip "dup-tip"))
     ((%sym 'aset) (ring) 0 (help-event tip))
     (let ((c0 (symbol-value 'num-nonmacro-input-events)))
       (record-char (help-event tip))
       (check "dispatch/dup-idx" 1 (ridx))
       (check "dispatch/dup-total" 1 (rtotal))
       (check "dispatch/dup-slot-kept" #t (equal? (help-event tip) (rref 0)))
       (check "dispatch/dup-counter" (+ c0 1)
              (symbol-value 'num-nonmacro-input-events))))))

;;; --- 3. record-char port: ring wrap-around (cr.org Finding 4) ---------
;;; 3a. write-back index-advance wrap: append at index lossage_limit-1
;;; wraps the index back to 0 (full ring keeps total pinned at limit).
(with-ring-state
 (lambda ()
   (let ((lim (rlimit)))
     (set-idx! (- lim 1)) (set-total! lim)
     (record-char 65)
     (check "wrap/append-slot" 65 (rref (- lim 1)))
     (check "wrap/append-index-wraps" 0 (ridx))
     (check "wrap/append-total-pinned" lim (rtotal)))))

;;; 3b. record-char-recorded's backward-walk wrap: at index 0 the previous
;;; ring slot is lossage_limit-1.  A help-echo stored there dedups a repeat
;;; (recorded = 1) — proving the ix1 walk wraps without touching slot 0.
(with-ring-state
 (lambda ()
   (let* ((lim (rlimit))
          (tip "wrap-tip"))
     (set-idx! 0) (set-total! 1)
     ((%sym 'aset) (ring) (- lim 1) (help-event tip))
     (record-char (help-event tip))
     (check "wrap/dedup-idx" 0 (ridx))
     (check "wrap/dedup-total" 1 (rtotal))
     (check "wrap/dedup-slot-kept" #t
            (equal? (help-event tip) (rref (- lim 1)))))))

;;; --- 4. --record-recent-keys-cmd-pseudo-event: (nil . CMD) append -----
;;; Drives the C DEFUN directly.  It now dispatches into
;;; record-cmd-pseudo-event!, which reuses record-char-write-back — so
;;; both writers produce the same plain-key append shape.  Note it does
;;; NOT bump num-nonmacro-input-events (matching the C pseudo-event body).
(with-ring-state
 (lambda ()
   (set-idx! 0) (set-total! 0)
   (let ((c0 (symbol-value 'num-nonmacro-input-events)))
     ((%sym '--record-recent-keys-cmd-pseudo-event) 'm17-cmd)
     (check "pseudo/ring-slot" (cons #nil 'm17-cmd) (rref 0))
     (check "pseudo/index-advance" 1 (ridx))
     (check "pseudo/total-incr" 1 (rtotal))
     (check "pseudo/counter-not-bumped" c0
            (symbol-value 'num-nonmacro-input-events)))))

;;; --- 5. --record-recent-keys-cmd-pseudo-event: ring wrap --------------
;;; Appending at index lossage_limit-1 wraps the index back to 0, same as
;;; record_char's plain-key append (section 3a) — proving both writers go
;;; through the same write-back wrap math.
(with-ring-state
 (lambda ()
   (let ((lim (rlimit)))
     (set-idx! (- lim 1)) (set-total! lim)
     ((%sym '--record-recent-keys-cmd-pseudo-event) 'm17-cmd2)
     (check "pseudo-wrap/slot" (cons #nil 'm17-cmd2) (rref (- lim 1)))
     (check "pseudo-wrap/index-wraps" 0 (ridx))
     (check "pseudo-wrap/total-pinned" lim (rtotal)))))
