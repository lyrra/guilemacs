;;; test-m21-read-key-sequence.scm --- M21 imp-1 parity corpus.
;;;
;;; Proves that the two setup functions for the three keyremaps
;;; (indec / fkey / keytran) at the start of a key-sequence read are
;;; behavior-identical:
;;;
;;;   rks-setup-replay-entire-sequence!   (pure Scheme, read-key-sequence.scm:580)
;;;   rks-setup-replay-entire-sequence-c! (calls C --rks-init-keyremaps,
;;;                                       keyboard.c:10563)
;;;
;;; Both write parent = map = <the new parent map> and start = end = 0
;;; into the *same kind* of <keyremap> record.  The C path only does
;;; anything when a state is pushed onto rks_state_stack (rks_keyremap_store
;;; returns early when rks_state_depth is 0), so we push a state with
;;; --rks-state-stack-push first, else the check would compare two no-ops.
;;;
;;; Reaches unexported bindings with Guile's @@ (rks-state-fkey/-keytran/-indec,
;;; keyremap-parent/-map/-start/-end are deliberately not exported — the module
;;; header says so).  This idiom is already used in test-m14-predicates.scm and
;;; test-kbd-dispatch.scm.  The C state-stack push/pop is reached via
;;; (symbol-function '--rks-state-stack-push) / '--rks-state-stack-pop.
;;;
;;; Sourced by test/keyboard/test-m21-read-key-sequence.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback from elisp.

(use-modules (emacs read-key-sequence))
(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))

;; Unexported bindings of (emacs read-key-sequence).
(define-syntax-rule (@@rk sym)
  (@@ (emacs read-key-sequence) sym))
;; explicit accessor names (srfi-9 auto-generated, not first-class in elisp
;; but fine from Scheme):
(define rks-state-fkey    (@@rk rks-state-fkey))
(define rks-state-keytran (@@rk rks-state-keytran))
(define rks-state-indec   (@@rk rks-state-indec))
(define keyremap-parent   (@@rk keyremap-parent))
(define keyremap-map      (@@rk keyremap-map))
(define keyremap-start    (@@rk keyremap-start))
(define keyremap-end      (@@rk keyremap-end))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (%sym name)
  (symbol-function name))

(define %push (delay (%sym '--rks-state-stack-push)))
(define %pop  (delay (%sym '--rks-state-stack-pop)))
(define %c-kboard-input-decode-map      (delay (%sym 'kboard-input-decode-map)))
(define %c-kboard-local-function-key-map (delay (%sym 'kboard-local-function-key-map)))

;;; Snapshot one <keyremap> record as a plain list.
(define (keyremap-snapshot kr)
  (list (keyremap-parent kr)
        (keyremap-map kr)
        (keyremap-start kr)
        (keyremap-end kr)))

;;; The three input maps: the live current-kboard maps and the global
;;; key-translation-map that both setup functions read.
(define (input-maps)
  (let ((kb ((%sym 'current-kboard))))
    (list ((force %c-kboard-input-decode-map) kb)
          ((force %c-kboard-local-function-key-map) kb)
          (symbol-value 'key-translation-map))))

(define (fkey-tran-indec state)
  (list (rks-state-fkey state)
        (rks-state-keytran state)
        (rks-state-indec state)))

;;; --- 1. Parity: stub-explicit, live current-kboard maps -------------
;;; Run both setup functions on fresh states and compare the three
;;; keyremap snapshots field-for-field.  The C variant is driven with a
;;; pushed state (the gotcha in brief.org Task 2).  Both read the live
;;; current-kboard maps, so this catches a current-kboard timing
;;; difference (Risk 3).
(let* ((state-a (make-rks-state))
       (state-b (make-rks-state))
       (maps (input-maps)))
  ;; state-a: pure Scheme path.
  (rks-setup-replay-entire-sequence! state-a)
  ;; state-b: C path, via the pushed state stack.
  ((force %push) state-b)
  (rks-setup-replay-entire-sequence-c!)
  ((force %pop))
  (let ((slots '("fkey" "keytran" "indec"))
        (a (map keyremap-snapshot (fkey-tran-indec state-a)))
        (b (map keyremap-snapshot (fkey-tran-indec state-b))))
    (for-each
     (lambda (name sa sb)
       (check (string-append "m21/parity-live/" name)
              sa sb))
     slots a b)
    ;; Each parent == map == the corresponding live input map.
    (check "m21/parity-live/indec-parent-is-input-map"
           (car maps) (keyremap-parent (rks-state-indec state-a)))
    (check "m21/parity-live/fkey-parent-is-input-map"
           (cadr maps) (keyremap-parent (rks-state-fkey state-a)))
    (check "m21/parity-live/keytran-parent-is-input-map"
           (caddr maps) (keyremap-parent (rks-state-keytran state-a)))
    ;; parent == map within each keyremap, and start == end == 0.
    (for-each
     (lambda (name state)
       (for-each
        (lambda (slot)
          (let* ((kr (case slot
                       ((indec) (rks-state-indec state))
                       ((fkey)  (rks-state-fkey state))
                       ((keytran) (rks-state-keytran state))))
                 (p (keyremap-parent kr))
                 (m (keyremap-map kr))
                 (s (keyremap-start kr))
                 (e (keyremap-end kr)))
            (check (format #f "m21/~a/~a-parent-eq-map" name slot)
                   #t (eq? p m))
            (check (format #f "m21/~a/~a-start-zero" name slot) 0 s)
            (check (format #f "m21/~a/~a-end-zero" name slot) 0 e)))
        '(indec fkey keytran)))
     '("parity-live/a" "parity-live/b")
     (list state-a state-b))))

;;; --- 2. Explicit stub keymaps ----------------------------------------
;;; Repeat with explicit stub keymaps so the check is not hostage to
;;; whatever the live current-kboard happens to be.  Both setup functions
;;; read the live current-kboard maps unconditionally, so to use stub
;;; maps we rebase the state's keyremaps directly (what the pure-Scheme
;;; setup does) and drive the C path with --rks-init-keyremaps fed the
;;; same stubs, then compare — this pins the parent/map equality contract
;;; independent of live kboard contents.
(define (make-stub-map name)
  (let ((m ((%sym 'make-sparse-keymap))))
    ((%sym 'define-key) m (vector (char->integer #\x)) name)
    m))

(let* ((stub-indec   (make-stub-map 'stub-indec))
       (stub-fkey    (make-stub-map 'stub-fkey))
       (stub-keytran (make-stub-map 'stub-keytran))
       (state-a (make-rks-state))
       (state-b (make-rks-state)))
  ;; state-a: pure Scheme path — but rebase to stubs first so both paths
  ;; start from the same parent (the setup functions would otherwise
  ;; overwrite with live maps; here we directly exercise the rebase
  ;; contract that both setup functions rely on).
  (keyremap-rebase! (rks-state-indec state-a) stub-indec)
  (keyremap-rebase! (rks-state-fkey state-a)  stub-fkey)
  (keyremap-rebase! (rks-state-keytran state-a) stub-keytran)
  ;; state-b: C path with the same stub maps fed to --rks-init-keyremaps.
  ((force %push) state-b)
  ((%sym '--rks-init-keyremaps) stub-indec stub-fkey stub-keytran)
  ((force %pop))
  (let ((slots '("fkey" "keytran" "indec"))
        (a (map keyremap-snapshot (fkey-tran-indec state-a)))
        (b (map keyremap-snapshot (fkey-tran-indec state-b))))
    (for-each
     (lambda (name sa sb)
       (check (string-append "m21/parity-stub/" name)
              sa sb))
     slots a b)
    (check "m21/parity-stub/indec-map-is-stub"
           stub-indec (keyremap-map (rks-state-indec state-a)))
    (check "m21/parity-stub/fkey-map-is-stub"
           stub-fkey (keyremap-map (rks-state-fkey state-a)))
    (check "m21/parity-stub/keytran-map-is-stub"
           stub-keytran (keyremap-map (rks-state-keytran state-a)))))
