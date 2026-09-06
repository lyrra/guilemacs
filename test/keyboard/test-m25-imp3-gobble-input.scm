;;; test-m25-imp3-gobble-input.scm --- M25 imp-3 (emacs gobble) test corpus.
;;;
;;; Covers the M25 imp-3 cutover (brief.org M25): the terminal_list walk
;;; of src/keyboard.c gobble_input moved into (emacs gobble) as
;;; gobble-input!.  gobble_input is now a thin dispatcher; four new
;;; single-purpose C shims stay C: --terminal-read-socket-hook-p,
;;; --terminal-read-socket-hook! (which owns the nr == -2 terminal-death
;;; arm, possibly terminate_due_to_signal), --pending-signals-set!, and
;;; --frame-make-pointer-visible!.  This corpus exercises the moved
;;; walk logic with the shims and the terminal/frame helpers stubbed:
;;;
;;;   - walk order: hook-having terminals visited newest-first (matching
;;;     physical terminal_list, not terminal-list's own order); a
;;;     hookless terminal is skipped without any --input-blocked-p call;
;;;   - early-stop: when input is blocked on a hook terminal, no later
;;;     terminal is visited and --pending-signals-set! is called once;
;;;   - drain accumulation + pointer-visible: per-terminal nread sums
;;;     across the walk and --frame-make-pointer-visible! runs once per
;;;     frame on a clean (nr 0) drain;
;;;   - error masking: an errored drain with total 0 yields -1; a
;;;     positive read elsewhere wins over an error;
;;;   - event storage: a drain ie-smob whose kind is not NO_EVENT is
;;;     stored via kbd-buffer-store-event! exactly once;
;;;   - cutover: gobble-input! is an exported procedure.
;;;
;;; gobble.scm references its C primitives through defelisp delays
;;; ((force %--...)), so these tests stub those delays by replacing them
;;; inside the (emacs gobble) module (module-set!), restoring after —
;;; the same stub mechanism test-m25-imp2-async-input.scm uses.  Every
;;; stub is restored in a dynamic-wind unwind, so nothing leaks into
;;; later corpora.
;;;
;;; Sourced by test/keyboard/test-m25-imp3-gobble-input.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback from
;;; elisp.  See brief.org M25 imp-3.
;;;
;;; Fake terminals and frames are Scheme symbols, so eq? distinguishes
;;; them without touching the real C terminal/frame lists.

(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))
(use-modules (emacs gobble))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

;;; --- Stub helpers ----------------------------------------------------

(define gobble-mod (resolve-module '(emacs gobble)))

;; Replace the defelisp delay NAME in (emacs gobble) so that
;; (force NAME) yields PROC, restoring the original delay after THUNK.
(define (with-gobble-delay! name proc thunk)
  (let ((old (module-ref gobble-mod name)))
    (dynamic-wind
      (lambda () (module-set! gobble-mod name (delay proc)))
      thunk
      (lambda () (module-set! gobble-mod name old)))))

;; Apply several with-gobble-delay! stubs at once (flattened to avoid
;; the paren imbalance of deep nesting).  PAIRS is a list of (name proc)
;; pairs, all stubbed for the duration of THUNK.
(define (with-many-delays! pairs thunk)
  (if (null? pairs)
      (thunk)
      (with-gobble-delay! (caar pairs) (cadar pairs)
        (lambda () (with-many-delays! (cdr pairs) thunk)))))

(define order '())
(define (record! x) (set! order (append order (list x))))
(define (reset-order!) (set! order '()))

;;; --- 1. Walk order + hookless skip ------------------------------------
;;; gobble-input! walks (reverse (terminal-list)), i.e. newest-first.
;;; Stub terminal-list to an oldest-first value (t1 oldest ... t4
;;; newest); the walk visits t4 t3 t2 t1.  Only t2 is hookless, so it
;;; must be skipped without reaching --input-blocked-p.  Every other
;;; terminal is drained; --input-blocked-p is called once per hook
;;; terminal (right before its drain).  So for newest-first (t4 t3 t1),
;;; record a checked-blocked step before each drain.
(reset-order!)
(with-many-delays!
 (list
  (list '%terminal-list (lambda () '(t1 t2 t3 t4)))
  (list '%--terminal-read-socket-hook-p
        (lambda (term) (if (eq? term 't2) #nil #t)))
  (list '%--input-blocked-p
        (lambda () (record! 'checked-blocked) #nil))
  (list '%--terminal-read-socket-hook!
        (lambda (term) (record! (list 'drain term)) '(0 0 no-quit)))
  (list '%--ie-kind (lambda (ie) 0))
  (list '%frame-list (lambda () '())))
 (lambda ()
   (gobble-input!)
   ;; drains happen newest-first among hook-having terminals
   (check "gobble-input!/walk-order-newest-first"
          '((drain t4) (drain t3) (drain t1))
          (filter (lambda (s) (and (pair? s) (eq? (car s) 'drain))) order))
   ;; --input-blocked-p ran exactly once per hook terminal (3), and the
   ;; hookless t2 was never reached.
   (check "gobble-input!/hookless-skip-no-input-blocked"
          '(checked-blocked checked-blocked checked-blocked)
          (filter (lambda (s) (eq? s 'checked-blocked)) order))))

;;; --- 2. Early-stop rule ----------------------------------------------
;;; A hook-having terminal that is blocked stops the whole walk: no
;;; later terminal is visited at all, and --pending-signals-set! is
;;; called exactly once.  Newest-first order (e1 e2 e3); e1 blocked.
(reset-order!)
(with-many-delays!
 (list
  (list '%terminal-list (lambda () '(e3 e2 e1)))
  (list '%--terminal-read-socket-hook-p (lambda (term) #t))
  (list '%--input-blocked-p (lambda () #t))
  (list '%--terminal-read-socket-hook!
        (lambda (term) (record! (list 'drain term)) '(0 0 no-quit)))
  (list '%--pending-signals-set!
        (lambda () (record! 'pending-set!) #nil)))
 (lambda ()
   (check "gobble-input!/early-stop-value"
          0 (gobble-input!))
   (check "gobble-input!/early-stop-no-drain"
          '() (filter (lambda (s) (and (pair? s) (eq? (car s) 'drain))) order))
   (check "gobble-input!/early-stop-pending-set-once"
          '(pending-set!) order)))

;;; --- 3. Drain accumulation + pointer-visible --------------------------
;;; Two hook-having terminals each end their drain cleanly (nr 0), with
;;; nread 3 and 2.  gobble-input! sums them to 5.  A clean drain makes
;;; --frame-make-pointer-visible! run once per frame on that terminal:
;;; t1 owns f1 f2, t2 owns f3.  Newest-first order visits t1 then t2.
(reset-order!)
(with-many-delays!
 (list
  (list '%terminal-list (lambda () '(t2 t1)))
  (list '%--terminal-read-socket-hook-p (lambda (term) #t))
  (list '%--input-blocked-p (lambda () #nil))
  (list '%--terminal-read-socket-hook!
        (lambda (term)
          (record! (list 'drain term))
          (if (eq? term 't1) '(3 0 no-quit) '(2 0 no-quit))))
  (list '%--ie-kind (lambda (ie) 0))
  (list '%frame-list (lambda () '(f1 f2 f3)))
  (list '%frame-terminal
        (lambda (frame)
          (if (eq? frame 'f3) 't2 't1)))
  (list '%--frame-make-pointer-visible!
        (lambda (frame) (record! (list 'show frame)) #nil)))
 (lambda ()
   (check "gobble-input!/drain-sums-across-terminals"
          5 (gobble-input!))
   (check "gobble-input!/pointer-visible-each-frame-once"
          '((show f1) (show f2) (show f3))
          (filter (lambda (s) (and (pair? s) (eq? (car s) 'show))) order))))

;;; --- 4. Error masking -------------------------------------------------
;;; 4a: a single drain that errors (nr -1) with total 0 overall → -1.
(with-many-delays!
 (list
  (list '%terminal-list (lambda () '(err)))
  (list '%--terminal-read-socket-hook-p (lambda (term) #t))
  (list '%--input-blocked-p (lambda () #nil))
  (list '%--terminal-read-socket-hook!
        (lambda (term) '(0 -1 no-quit)))
  (list '%--ie-kind (lambda (ie) 0))
  (list '%frame-list (lambda () '())))
 (lambda ()
   (check "gobble-input!/error-masked-when-nothing-read"
          -1 (gobble-input!))))

;;; 4b: one terminal errors (-1) but another reads a positive count; the
;;; positive total wins, not -1.  Newest-first visits t1 (reads 4) then
;;; t2 (errors).
(with-many-delays!
 (list
  (list '%terminal-list (lambda () '(t2 t1)))
  (list '%--terminal-read-socket-hook-p (lambda (term) #t))
  (list '%--input-blocked-p (lambda () #nil))
  (list '%--terminal-read-socket-hook!
        (lambda (term)
          (if (eq? term 't1) '(4 0 no-quit) '(0 -1 no-quit))))
  (list '%--ie-kind (lambda (ie) 0))
  (list '%frame-list (lambda () '(f1)))
  (list '%frame-terminal (lambda (frame) 't1))
  (list '%--frame-make-pointer-visible! (lambda (frame) #nil)))
 (lambda ()
   (check "gobble-input!/positive-read-wins-over-error"
          4 (gobble-input!))))

;;; --- 5. Event storage -------------------------------------------------
;;; A drain whose returned ie-smob has kind != NO_EVENT triggers exactly
;;; one kbd-buffer-store-event! call with that smob (and the hold-quit
;;; flag #f).  Stub the user-signal list empty so store-user-signal-events!
;;; (called at the top of gobble-input!) cannot also touch the store.
(reset-order!)
(with-many-delays!
 (list
  (list '%--user-signal-list (lambda () '()))
  (list '%terminal-list (lambda () '(q)))
  (list '%--terminal-read-socket-hook-p (lambda (term) #t))
  (list '%--input-blocked-p (lambda () #nil))
  (list '%--terminal-read-socket-hook! (lambda (term) '(0 0 quit-ie)))
  (list '%--ie-kind (lambda (ie) (if (eq? ie 'quit-ie) 7 0)))
  (list '%--frame-make-pointer-visible! (lambda (frame) #nil))
  (list '%frame-list (lambda () '()))
  (list '%kbd-buffer-store-event!
        (lambda (ie hold-quit) (record! (list 'store ie hold-quit)) #nil)))
 (lambda ()
   (gobble-input!)
   (check "gobble-input!/event-stored-exactly-once"
          '((store quit-ie #f)) order)))

;;; --- 6. Cutover wiring ------------------------------------------------
;;; gobble_input (C) must resolve the (emacs gobble) public ref
;;; gobble-input!.  Verify it is an exported procedure of the module.
(check "gobble/exported-gobble-input!" #t
       (procedure? (module-ref (resolve-interface '(emacs gobble))
                               'gobble-input!)))
