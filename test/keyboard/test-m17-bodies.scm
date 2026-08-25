;;; test-m17-bodies.scm --- M17 imp-2 test corpus for the Scheme
;;; record-char procedure in (emacs recent-keys), a port of C
;;; record_char (src/keyboard.c:4386-4529).
;;;
;;; Sourced by test/keyboard/test-m17-bodies.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp.  See docs/m17-plan.org §imp-2 and brief.org.
;;;
;;; record-char reads/writes the C-owned recent-keys ring through the
;;; imp-1 shims plus aref/aset/symbol-value/set-symbol-value!/
;;; store-kbd-macro-event.  Every sub-test that mutates the ring or the
;;; guarded elisp vars (record-all-keys, inhibit--record-char,
;;; executing-kbd-macro, num-nonmacro-input-events) runs inside a
;;; with-ring-state dynamic-wind that resets the ring and restores the
;;; vars, so ring-position math stays deterministic (same discipline as
;;; test-m17-shims.scm and test-m16-bodies.scm).

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
;;; value read back from an elisp vector slot (same helper as
;;; test-m16-bodies.scm).
(define (elist . items)
  (let loop ((i items))
    (if (null? i) #nil (cons (car i) (loop (cdr i))))))

(define (no-error? thunk)
  (catch #t
    (lambda () (thunk) #t)
    (lambda (key . args) (list 'error key args))))

;;; --- Ring access helpers --------------------------------------------
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

;;; Event constructors.  A help-echo event's help string is its caddr
;;; (C: help = Fcar_safe (Fcdr_safe (XCDR (c)))); a mouse-movement event's
;;; window is its cadr (C: window = Fcar_safe (Fcar_safe (XCDR (c)))).
(define (help-event tip) (list 'help-echo 'win tip 'other))
(define (mouse-event win . xy) (apply list 'mouse-movement win xy))

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

;;; --- 0. DEFVAR_INT write round-trip (brief step 1) ------------------
;;; record-char bumps num-nonmacro-input-events via set-symbol-value!.
;;; Verify a set-symbol-value! write round-trips on the DEFVAR_INT before
;;; relying on it deep inside the dedup logic.
(let ((orig (symbol-value 'num-nonmacro-input-events)))
  (set-symbol-value! 'num-nonmacro-input-events (+ orig 1))
  (check "num-nonmacro/roundtrip" (+ orig 1)
         (symbol-value 'num-nonmacro-input-events))
  (set-symbol-value! 'num-nonmacro-input-events orig)
  (check "num-nonmacro/restore" orig (symbol-value 'num-nonmacro-input-events)))

;;; --- 1. Registration: record-char resolves from (emacs recent-keys) --
;;; Not yet registered as an elisp function (that is imp-3 cutover), so
;;; resolve it as a module procedure.
(define m17-mod (resolve-module '(emacs recent-keys)))
(check "record-char/resolves" #t (procedure? (module-ref m17-mod 'record-char)))

;;; --- 2. Plain-key append --------------------------------------------
(with-ring-state
 (lambda ()
   (set-idx! 2) (set-total! 2)
   ((%sym 'aset) (ring) 0 97)
   ((%sym 'aset) (ring) 1 98)
   (let ((c0 (symbol-value 'num-nonmacro-input-events)))
     (record-char 99)
     (check "plain/ring-slot" 99 (rref 2))
     (check "plain/index-advance" 3 (ridx))
     (check "plain/total-incr" 3 (rtotal))
     (check "plain/counter-incr" (+ c0 1)
            (symbol-value 'num-nonmacro-input-events)))))

;;; --- 3. Cons event append: copied via copy-sequence ----------------
(with-ring-state
 (lambda ()
   (set-idx! 0) (set-total! 0)
   (let ((ev '(foo bar)))
     (record-char ev)
     (let ((stored (rref 0)))
       ;; copy-sequence yields an elisp list (ends in #nil), so compare
       ;; against an elisp-built list, not a bare guile literal.
       (check "cons/equal-stored" #t (equal? (elist 'foo 'bar) stored))
       (check "cons/not-eq-copied" #t (not (eq? ev stored)))))))

;;; --- 4. store-kbd-macro-event calls --------------------------------
;;; Called with c for a plain key; NOT called for a help-echo or
;;; mouse-movement event.  Shadow the function (restored by with-ring-state
;;; only for the elisp vars — we restore it by hand here too).
(with-ring-state
 (lambda ()
   (set-idx! 0) (set-total! 0)
   (let ((calls '()) (saved (symbol-function 'store-kbd-macro-event)))
     (dynamic-wind
       (lambda () #f)
       (lambda ()
         (set-symbol-function! 'store-kbd-macro-event
                               (lambda (c) (set! calls (cons c calls))))
         (record-char 65)
         (check "store/plain-called" #t (pair? calls))
         (check "store/plain-arg" 65 (and (pair? calls) (car calls)))
         (set! calls '())
         (record-char (help-event "tip"))
         (check "store/help-not-called" '() calls)
         (set! calls '())
         (record-char (mouse-event 'W 1 2))
         (check "store/mouse-not-called" '() calls))
       (lambda () (set-symbol-function! 'store-kbd-macro-event saved))))))

;;; --- 5. Help-echo dedup: recorded = 1 leaves the ring unchanged -----
;;; 5a. non-string help payload.
(with-ring-state
 (lambda ()
   (set-idx! 3) (set-total! 3)
   ((%sym 'aset) (ring) 0 97) ((%sym 'aset) (ring) 1 98) ((%sym 'aset) (ring) 2 99)
   (let ((c0 (symbol-value 'num-nonmacro-input-events)))
     (record-char (list 'help-echo 'win 42 'other))
     (check "helpdedup/nonstring-slot0" 97 (rref 0))
     (check "helpdedup/nonstring-idx" 3 (ridx))
     (check "helpdedup/nonstring-total" 3 (rtotal))
     (check "helpdedup/nonstring-counter" (+ c0 1)
            (symbol-value 'num-nonmacro-input-events)))))

;;; 5b. repeat of the previous help-echo's string.
(with-ring-state
 (lambda ()
   (set-idx! 1) (set-total! 1)
   (let ((tip "same-tip"))
     ((%sym 'aset) (ring) 0 (help-event tip))
     (let ((c0 (symbol-value 'num-nonmacro-input-events)))
       (record-char (help-event tip))
       (check "helpdedup/dup-idx" 1 (ridx))
       (check "helpdedup/dup-total" 1 (rtotal))
       (check "helpdedup/dup-slot-kept" #t (equal? (help-event tip) (rref 0)))
       (check "helpdedup/dup-counter" (+ c0 1)
              (symbol-value 'num-nonmacro-input-events))))))

;;; --- 6. Help-echo pop: recorded = -1 / -2 ---------------------------
;;; 6a. mouse-movement then help-echo, repeated help -> recorded = -1:
;;; the mouse-movement slot is popped to nil, index/total move back.
(with-ring-state
 (lambda ()
   (set-idx! 2) (set-total! 2)
   (let ((tip "pop-tip"))
     ((%sym 'aset) (ring) 1 (mouse-event 'W 1 2))
     ((%sym 'aset) (ring) 0 (help-event tip))
     (record-char (help-event tip))
     (check "helppop/m1-slot-nil" #nil (rref 1))
     (check "helppop/m1-idx" 1 (ridx))
     (check "helppop/m1-total" 1 (rtotal)))))

;;; 6b. two mouse-movements then help-echo, repeated help -> recorded = -2:
;;; both mouse-movement slots are popped.
(with-ring-state
 (lambda ()
   (set-idx! 3) (set-total! 3)
   (let ((tip "pop-tip2"))
     ((%sym 'aset) (ring) 2 (mouse-event 'W 1 2))
     ((%sym 'aset) (ring) 1 (mouse-event 'W 3 4))
     ((%sym 'aset) (ring) 0 (help-event tip))
     (record-char (help-event tip))
     (check "helppop/m2-slot-nil" #nil (rref 2))
     (check "helppop/m2-slot-nil2" #nil (rref 1))
     (check "helppop/m2-idx" 1 (ridx))
     (check "helppop/m2-total" 1 (rtotal)))))

;;; --- 7. Mouse-movement in-place replace ----------------------------
;;; Two prior mouse-movement events on the same window, then a third:
;;; the slot at old ix1 is overwritten (eq? — stored directly, not
;;; copied) and index/total do not advance.
(with-ring-state
 (lambda ()
   (set-idx! 2) (set-total! 2)
   ((%sym 'aset) (ring) 1 (mouse-event 'W 1 2))
   ((%sym 'aset) (ring) 0 (mouse-event 'W 3 4))
   (let ((c (mouse-event 'W 5 6)))
     (record-char c)
     (check "mouse/inplace-eq" #t (eq? c (rref 1)))
     (check "mouse/inplace-idx" 2 (ridx))
     (check "mouse/inplace-total" 2 (rtotal)))))

;;; --- 8. executing-kbd-macro guard ----------------------------------
;;; With a macro executing, a plain key changes nothing: no ring write,
;;; no index/total move, no counter bump, and the store stub never fires.
(with-ring-state
 (lambda ()
   (set-symbol-value! 'executing-kbd-macro 'some-macro)
   (set-idx! 5) (set-total! 5)
   ((%sym 'aset) (ring) 4 120)
   (let ((c0 (symbol-value 'num-nonmacro-input-events))
         (saved (symbol-function 'store-kbd-macro-event))
         (calls '()))
     (dynamic-wind
       (lambda () #f)
       (lambda ()
         (set-symbol-function! 'store-kbd-macro-event
                               (lambda (c) (set! calls (cons c calls))))
         (record-char 65)
         (check "macro/ring-slot" 120 (rref 4))
         (check "macro/idx" 5 (ridx))
         (check "macro/total" 5 (rtotal))
         (check "macro/counter" c0 (symbol-value 'num-nonmacro-input-events))
         (check "macro/store-not-called" '() calls))
       (lambda () (set-symbol-function! 'store-kbd-macro-event saved))))))

;;; 8b. The mouse-movement in-place replace is NOT macro-gated: it still
;;; happens during macro playback, but index/total/counter stay put.
(with-ring-state
 (lambda ()
   (set-symbol-value! 'executing-kbd-macro 'some-macro)
   (set-idx! 2) (set-total! 2)
   ((%sym 'aset) (ring) 1 (mouse-event 'W 1 2))
   ((%sym 'aset) (ring) 0 (mouse-event 'W 3 4))
   (let ((c0 (symbol-value 'num-nonmacro-input-events))
         (c (mouse-event 'W 5 6)))
     (record-char c)
     (check "macro-mouse/inplace-eq" #t (eq? c (rref 1)))
     (check "macro-mouse/idx" 2 (ridx))
     (check "macro-mouse/total" 2 (rtotal))
     (check "macro-mouse/counter" c0 (symbol-value 'num-nonmacro-input-events)))))

;;; --- 9. Dribble: no dribble file open -> no signal -----------------
(with-ring-state
 (lambda ()
   (check "dribble/no-open-no-signal" #t
          (no-error? (lambda () (record-char 65))))
   (check "dribble/open-p-nil" #nil ((%sym '--dribble-open-p)))))
