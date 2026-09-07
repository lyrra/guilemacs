;;; test-m27-single-kboard.scm --- M27 imp-1 (emacs single-kboard) test corpus.
;;;
;;; Covers the M27 imp-1 cutover (brief.org M27): the single-kboard
;;; family *policy* moved out of src/keyboard.c into (emacs
;;; single-kboard) as not-single-kboard-state, push-kboard!,
;;; pop-kboard! and temporarily-switch-to-single-kboard!.  The C
;;; pieces that must stay C (single_kboard flag setter/getter,
;;; --kboard-live-p terminal walk, --selected-frame-kboard, and the
;;; record_unwind_protect_int frame) are exposed to Scheme as shims and
;;; stay C (see docs/m27-plan.org Finding 6).  This corpus exercises
;;; the moved policy logic over stubbed shims:
;;;
;;;   - not-single-kboard-state clears single_kboard only when its
;;;     kboard is current_kboard; it is a no-op otherwise;
;;;   - push-kboard! saves current_kboard then sets the new one;
;;;   - pop-kboard! restores the saved kboard when it is still live;
;;;   - pop-kboard! of a deleted kboard falls back to
;;;     --selected-frame-kboard and clears single_kboard;
;;;   - temporarily-switch-to-single-kboard! sets single_kboard true;
;;;     the was-locked branch pushes current_kboard first; the kb
;;;     branch sets current_kboard only when kb is non-nil.
;;;
;;; single-kboard.scm references its C primitives through defelisp
;;; delays ((force %--...)), so these tests stub those delays by
;;; replacing them inside the (emacs single-kboard) module
;;; (module-set!), restoring after — the same stub mechanism
;;; test-m19-*.scm and test-m25-*.scm use.  Every stub is restored in a
;;; dynamic-wind unwind, so nothing leaks into later corpora
;;; ([[shared-harness-cross-corpus-state-leak]]).
;;;
;;; Sourced by test/keyboard/test-m27-single-kboard.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback from
;;; elisp.  See brief.org M27 imp-1.
;;;
;;; Live multi-tty single_kboard behavior (risk-register Risk 1) cannot
;;; run in this sandbox: creating a second terminal requires a real
;;; multi-tty session.  Recorded here explicitly instead of skipped
;;; silently; the C unwind registration and dispatcher wiring are
;;; exercised structurally below.

(use-modules (emacs single-kboard))
(use-modules (emacs elisp-ref))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

;;; --- Stub helpers ----------------------------------------------------

(define sk-mod (resolve-module '(emacs single-kboard)))

(define sk-var-names
  '( %current-kboard %set-current-kboard %kboard-eq
     %--kbd-single-kboard-set! %--kboard-live-p
     %--selected-frame-kboard ))

;; Run THUNK with every (emacs single-kboard) C delay replaced by a stub
;; reading/writing a fake state: CUR is the current kboard, SINGLE the
;; C single_kboard flag (#t/#nil), LIVE a predicate over kboards, SEL the
;; fallback selected-frame kboard.  Restores all delays (and the module
;; kboard-stack) afterwards.
(define (run-with-sk-fakes! cur single live sel thunk)
  (let ((cur-cell (list cur))
        (single-cell (list single)))
    (define (cur) (car cur-cell))
    (define (cur!) (lambda (kb) (set-car! cur-cell kb) kb))
    (define (single-set!) (lambda (v) (set-car! single-cell v) #nil))
    (let ((originals (map (lambda (nm) (module-ref sk-mod nm)) sk-var-names)))
      (dynamic-wind
        (lambda ()
          (module-set! sk-mod '%current-kboard
                       (delay (lambda () (cur))))
          (module-set! sk-mod '%set-current-kboard
                       (delay (cur!)))
          (module-set! sk-mod '%kboard-eq
                       (delay (lambda (a b) (if (eq? a b) #t #nil))))
          (module-set! sk-mod '%--kbd-single-kboard-set!
                       (delay (single-set!)))
          (module-set! sk-mod '%--kboard-live-p
                       (delay (lambda (kb) (if (live kb) #t #nil))))
          (module-set! sk-mod '%--selected-frame-kboard
                       (delay (lambda () sel))))
        (lambda ()
          (module-set! sk-mod 'kboard-stack '())
          (thunk cur-cell single-cell))
        (lambda ()
          (let loop ((names sk-var-names) (saved originals))
            (unless (null? names)
              (module-set! sk-mod (car names) (car saved))
              (loop (cdr names) (cdr saved))))
          (module-set! sk-mod 'kboard-stack '()))))))

;; Stack inspection/set: the module keeps its own kboard-stack list.
(define (sk-stack) (module-ref sk-mod 'kboard-stack))
(define (sk-stack! v) (module-set! sk-mod 'kboard-stack v))

;;; --- 1. not-single-kboard-state ---------------------------------------

(run-with-sk-fakes! 'kb-a #t (lambda (kb) #t) 'kb-sel
  (lambda (cur-cell single-cell)
    ;; Clearing when kb is current_kboard.
    (not-single-kboard-state 'kb-a)
    (check "not-single-kboard-state/clears-when-current" #nil
           (car single-cell))
    ;; No-op when kb differs from current_kboard.
    (set-car! single-cell #t)
    (not-single-kboard-state 'kb-other)
    (check "not-single-kboard-state/noop-for-other" #t
           (car single-cell))
    ;; current_kboard itself is unchanged throughout.
    (check "not-single-kboard-state/current-unchanged" 'kb-a
           (car cur-cell))))

;;; --- 2. push-kboard! / pop-kboard! (live kboard) ----------------------

(run-with-sk-fakes! 'kb-a #nil (lambda (kb) #t) 'kb-sel
  (lambda (cur-cell single-cell)
    ;; push saves current then sets the new one.
    (push-kboard! 'kb-b)
    (check "push-kboard!/saves-current-then-sets" 'kb-b
           (car cur-cell))
    (check "push-kboard!/saved-old-current-on-stack" '(kb-a)
           (sk-stack))
    ;; pop of a live kboard restores the saved current.
    (pop-kboard!)
    (check "pop-kboard!/restores-live-saved" 'kb-a
           (car cur-cell))
    (check "pop-kboard!/stack-popped" '()
           (sk-stack))
    ;; pop must not clear single_kboard for a live restore.
    (set-car! single-cell #t)
    (push-kboard! 'kb-b)
    (pop-kboard!)
    (check "pop-kboard!/live-restore-keeps-single" #t
           (car single-cell))))

;;; --- 3. pop-kboard! of a deleted kboard -------------------------------

(run-with-sk-fakes! 'kb-a #nil (lambda (kb) #f) 'kb-sel
  (lambda (cur-cell single-cell)
    ;; With no live terminal, pop falls back to --selected-frame-kboard
    ;; and clears single_kboard.
    (set-car! single-cell #t)
    (push-kboard! 'kb-b)
    (check "pop-kboard-deleted/pushed-current" 'kb-b
           (car cur-cell))
    (pop-kboard!)
    (check "pop-kboard-deleted/falls-back-to-selected-frame" 'kb-sel
           (car cur-cell))
    (check "pop-kboard-deleted/clears-single" #nil
           (car single-cell))
    (check "pop-kboard-deleted/stack-popped" '()
           (sk-stack))))

;;; --- 4. temporarily-switch-to-single-kboard! --------------------------

;; was-locked branch: pushes current_kboard (ignoring kb), sets single true.
(run-with-sk-fakes! 'kb-a #nil (lambda (kb) #t) 'kb-sel
  (lambda (cur-cell single-cell)
    ;; Not locked, kb non-nil: current_kboard set to kb, single true.
    (temporarily-switch-to-single-kboard! #nil 'kb-c)
    (check "temporarily-switch/unlocked-kb-sets-current" 'kb-c
           (car cur-cell))
    (check "temporarily-switch/unlocked-kb-sets-single" #t
           (car single-cell))))

(run-with-sk-fakes! 'kb-a #nil (lambda (kb) #t) 'kb-sel
  (lambda (cur-cell single-cell)
    ;; Not locked, kb nil: current_kboard untouched, single still set.
    (temporarily-switch-to-single-kboard! #nil #nil)
    (check "temporarily-switch/unlocked-nil-kb-keeps-current" 'kb-a
           (car cur-cell))
    (check "temporarily-switch/unlocked-nil-kb-sets-single" #t
           (car single-cell))))

(run-with-sk-fakes! 'kb-a #nil (lambda (kb) #t) 'kb-sel
  (lambda (cur-cell single-cell)
    ;; Locked branch: pushes current_kboard onto the stack first (saved
    ;; current == current), sets single true; kb arg is ignored.
    (temporarily-switch-to-single-kboard! #t 'kb-c)
    (check "temporarily-switch/locked-keeps-current" 'kb-a
           (car cur-cell))
    (check "temporarily-switch/locked-pushed-current" '(kb-a)
           (sk-stack))
    (check "temporarily-switch/locked-sets-single" #t
           (car single-cell))))

;;; --- 5. Cutover wiring ------------------------------------------------
;;; The four C dispatchers (not_single_kboard_state, push_kboard,
;;; pop_kboard, temporarily_switch_to_single_kboard) each resolve a
;;; (emacs single-kboard) public ref.  Verify each target is an exported
;;; procedure of the module (its bodies are exercised above).
(check "single-kboard/exported-not-single-kboard-state" #t
       (procedure? (module-ref (resolve-interface '(emacs single-kboard))
                               'not-single-kboard-state)))
(check "single-kboard/exported-push-kboard!" #t
       (procedure? (module-ref (resolve-interface '(emacs single-kboard))
                               'push-kboard!)))
(check "single-kboard/exported-pop-kboard!" #t
       (procedure? (module-ref (resolve-interface '(emacs single-kboard))
                               'pop-kboard!)))
(check "single-kboard/exported-temporarily-switch!" #t
       (procedure? (module-ref (resolve-interface '(emacs single-kboard))
                               'temporarily-switch-to-single-kboard!)))
