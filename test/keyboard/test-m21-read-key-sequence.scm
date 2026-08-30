;;; test-m21-read-key-sequence.scm --- M21 imp-1 + imp-2 parity corpus.
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

;;; --- 3. rks-keyremap-step!: direct unit checks -----------------------
;;; imp-2.  rks-keyremap-step! is the Scheme port of C keyremap_step +
;;; access_keymap_keyremap (src/keyboard.c:10601-10715).  It is NOT yet
;;; wired into the live C walk DEFUNs (that cutover is imp-3), so these
;;; are direct unit checks on the port.  There is no single-step C entry
;;; point to compare against (both C functions are static), so we check
;;; the documented C semantics directly.
;;;
;;; Live loop-level parity against the C --rks-walk-indec DEFUN is
;;; deferred to imp-3 (brief.org Open decision 2, item 1).  At imp-2 it
;;; is infeasible: --rks-walk-indec and --rks-keybuf-set both no-op
;;; unless a keybuf is pushed on the internal C rks_keybuf_stack, and the
;;; only code that pushes one is read_key_sequence itself
;;; (src/keyboard.c:10923) — imp-2 forbids adding a C push shim.  Instead
;;; section 3.11 runs a Scheme walk loop that mirrors the C --rks-walk-indec
;;; loop (`while (indec.end < rks_t)`) over rks-keyremap-step!, so the
;;; composed walk (submap descend + translate, mock_input accumulation,
;;; exhaustion) is exercised end to end.  See docs/m21-plan.org imp-2.
(define READ-KEY-ELTS (@@rk READ-KEY-ELTS))

(define (make-keybuf . events)
  ;; A READ-KEY-ELTS-length Scheme vector holding EVENTS at the front.
  (let ((kb (make-vector READ-KEY-ELTS #nil)))
    (let loop ((i 0) (ev events))
      (unless (null? ev)
        (vector-set! kb i (car ev))
        (loop (+ i 1) (cdr ev))))
    kb))

(define (caught-error thunk)
  ;; Runs THUNK, returns 'no-error if it returns, else (caught key args).
  (catch #t
    (lambda () (thunk) 'no-error)
    (lambda (key . args) (list 'caught key args))))

(define (front-vector kb n)
  ;; Copy the first N elements of keybuf KB into a fresh Scheme vector.
  (let ((v (make-vector n #nil)))
    (let loop ((i 0))
      (when (< i n)
        (vector-set! v i (vector-ref kb i))
        (loop (+ i 1))))
    v))

;;; --- 3.1 plain lookup: single key → two-key vector (diff > 0) -------
(let* ((m   (make-stub-map 'plain-lookup))
       (fkey (make-keyremap m))
       (kb   (make-keybuf (char->integer #\a))))
  ((%sym 'define-key) m (vector (char->integer #\a))
        (vector (char->integer #\b) (char->integer #\c)))
  (check "m21/step/plain-lookup/returns-diff"
         1 (rks-keyremap-step! fkey kb 1 #t #nil))
  (check "m21/step/plain-lookup/overwrites"
         (vector (char->integer #\b) (char->integer #\c))
         (front-vector kb 2))
  (check "m21/step/plain-lookup/start-end"
         '(2 2) (list (keyremap-start fkey) (keyremap-end fkey)))
  (check "m21/step/plain-lookup/map-reset"
         m (keyremap-map fkey)))

;;; --- 3.2 plain lookup: zero-length diff returns 0 (truthy) ----------
(let* ((m   (make-stub-map 'plain-lookup-zero))
       (fkey (make-keyremap m))
       (kb   (make-keybuf (char->integer #\a))))
  ((%sym 'define-key) m (vector (char->integer #\a))
        (vector (char->integer #\b)))
  (check "m21/step/plain-lookup-zero/returns-0"
         0 (rks-keyremap-step! fkey kb 1 #t #nil))
  (check "m21/step/plain-lookup-zero/b" (char->integer #\b)
         (vector-ref kb 0)))

;;; --- 3.3 submap continuation: key → submap → final binding ----------
(let* ((m   (make-stub-map 'submap-root))
       (m2  (make-stub-map 'submap-child))
       (fkey (make-keyremap m))
       (kb   (make-keybuf (char->integer #\a) (char->integer #\b))))
  ((%sym 'define-key) m (vector (char->integer #\a)) m2)
  ((%sym 'define-key) m2 (vector (char->integer #\b))
        (vector (char->integer #\c) (char->integer #\d) (char->integer #\e)))
  ;; step 1: descend into the submap, no translation yet.
  (check "m21/step/submap/step1-false" #f
         (rks-keyremap-step! fkey kb 2 #t #nil))
  (check "m21/step/submap/step1-map" m2 (keyremap-map fkey))
  (check "m21/step/submap/step1-end" 1 (keyremap-end fkey))
  ;; step 2: resolve the [a b] prefix in m2 → [c d e] (diff +1).
  (check "m21/step/submap/step2-returns-diff"
         1 (rks-keyremap-step! fkey kb 2 #t #nil))
  (check "m21/step/submap/step2-overwrites"
         (vector (char->integer #\c) (char->integer #\d) (char->integer #\e))
         (front-vector kb 3))
  (check "m21/step/submap/step2-start-end"
         '(3 3) (list (keyremap-start fkey) (keyremap-end fkey))))

;;; --- 3.4 autoload-shaped: symbol whose function cell is a keymap ----
;;; A key bound to a symbol whose function definition is a keymap takes
;;; the access_keymap_keyremap autoload branch (SYMBOLP + fboundp +
;;; KEYMAPP/array on the function cell).  autoload-do-load on a
;;; non-autoload keymap returns the keymap, so the symbol resolves to
;;; its function and the scan descends like a normal submap.
(let* ((m   (make-stub-map 'autoload-root))
       (m2  (make-stub-map 'autoload-child))
       (stub-sym (make-symbol "m21-autoload-stub"))
       (fkey (make-keyremap m))
       (kb   (make-keybuf (char->integer #\a) (char->integer #\b))))
  (set-symbol-function! stub-sym m2)
  ((%sym 'define-key) m (vector (char->integer #\a)) stub-sym)
  ((%sym 'define-key) m2 (vector (char->integer #\b))
        (vector (char->integer #\z)))
  ;; step 1: symbol → autoload branch → function cell (a keymap) → submap.
  (check "m21/step/autoload/step1-false" #f
         (rks-keyremap-step! fkey kb 2 #t #nil))
  (check "m21/step/autoload/step1-map" m2 (keyremap-map fkey))
  ;; step 2: resolve in the autoloaded keymap.  The [a b] prefix is
  ;; replaced by [z]: diff = 1 - (2 - 0) = -1, and z lands at index 0
  ;; (the caller adjusts its buffer-length counter by the diff).
  (check "m21/step/autoload/step2-returns-diff"
         -1 (rks-keyremap-step! fkey kb 2 #t #nil))
  (check "m21/step/autoload/step2-z" (char->integer #\z)
         (vector-ref kb 0)))

;;; --- 3.5 funcall branch: keymap entry is a function -----------------
;;; A key bound to a lambda is funcalled with PROMPT and its return value
;;; (a vector) is used as the remap.
(let* ((m   (make-stub-map 'funcall-valid))
       (fkey (make-keyremap m))
       (kb   (make-keybuf (char->integer #\a)))
       (fn   (list 'lambda '(prompt) (list 'vector (char->integer #\b) (char->integer #\c)))))
  ((%sym 'define-key) m (vector (char->integer #\a)) fn)
  (check "m21/step/funcall-valid/returns-diff"
         1 (rks-keyremap-step! fkey kb 1 #t "prompt"))
  (check "m21/step/funcall-valid/overwrites"
         (vector (char->integer #\b) (char->integer #\c))
         (front-vector kb 2)))

;;; --- 3.5b funcall branch: lambda reads current-key-remap-sequence -----
;;; Review Finding 1.  Inside the funcall, current-key-remap-sequence is
;;; bound to the slice keybuf[start..end] (inclusive) that was looked
;;; up.  For this single-key case that slice is the one-element vector
;;; #(a).  The lambda echoes the slice's first element (proving it read
;;; the *bound* slice, not stale data) plus one more key; the resulting
;;; remap [a c] proves the bind content too.
(let* ((m   (make-stub-map 'funcall-read-remap))
       (fkey (make-keyremap m))
       (kb   (make-keybuf (char->integer #\a)))
       (fn   (list 'lambda '(prompt)
                   (list 'vector
                         (list 'aref 'current-key-remap-sequence 0)
                         (char->integer #\c)))))
  ((%sym 'define-key) m (vector (char->integer #\a)) fn)
  ;; [a] slice → remap [a c] (len 2): diff = 2 - (1 - 0) = 1.
  (check "m21/step/funcall-read-remap/returns-diff"
         1 (rks-keyremap-step! fkey kb 1 #t "prompt"))
  ;; The leading 'a' in the result can only come from the bound slice.
  (check "m21/step/funcall-read-remap/overwrites"
         (vector (char->integer #\a) (char->integer #\c))
         (front-vector kb 2)))

;;; --- 3.6 funcall branch: invalid return value signals an error ------
(let* ((m   (make-stub-map 'funcall-invalid))
       (fkey (make-keyremap m))
       (kb   (make-keybuf (char->integer #\a)))
       (fn   (list 'lambda '(prompt) 42)))
  ((%sym 'define-key) m (vector (char->integer #\a)) fn)
  (check "m21/step/funcall-invalid/error" #t
         (not (eq? 'no-error
                   (caught-error
                    (lambda ()
                      (rks-keyremap-step! fkey kb 1 #t "prompt")))))))

;;; --- 3.7 "Key sequence too long" error ------------------------------
;;; input close to READ-KEY-ELTS plus a translation whose diff would
;;; overflow the buffer signals "Key sequence too long".
(let* ((m   (make-stub-map 'too-long))
       (fkey (make-keyremap m))
       (kb   (make-keybuf (char->integer #\a)))
       (fn   (list 'lambda '(prompt)
                   (vector (char->integer #\b) (char->integer #\c) (char->integer #\d)))))
  ((%sym 'define-key) m (vector (char->integer #\a)) fn)
  ;; input = READ-KEY-ELTS - 1, len = 3 → diff = 3 - 1 = 2,
  ;; READ-KEY-ELTS - input = 1 <= 2 → error.
  (check "m21/step/too-long/error" #t
         (not (eq? 'no-error
                   (caught-error
                    (lambda ()
                      (rks-keyremap-step! fkey kb (- READ-KEY-ELTS 1) #t "prompt")))))))

;;; --- 3.8 buffer shift: expansion shifts a trailing event up ---------
;;; 'a' → [c d] (len 2, diff +1) with a trailing event at index 1:
;;; the trailing event must shift up to index 2 before [c d] overwrites
;;; indices 0-1 (positive-diff shift runs high-to-low).
(let* ((m   (make-stub-map 'shift-expand))
       (fkey (make-keyremap m))
       (kb   (make-keybuf (char->integer #\a) (char->integer #\X))))
  ((%sym 'define-key) m (vector (char->integer #\a))
        (vector (char->integer #\c) (char->integer #\d)))
  (check "m21/step/shift-expand/returns-diff"
         1 (rks-keyremap-step! fkey kb 2 #t #nil))
  (check "m21/step/shift-expand/front"
         (vector (char->integer #\c) (char->integer #\d))
         (front-vector kb 2))
  (check "m21/step/shift-expand/trailing" (char->integer #\X)
         (vector-ref kb 2)))

;;; --- 3.9 buffer shift: contraction shifts a trailing event down -----
;;; 'a' → [] (len 0, diff -1): the trailing event at index 1 shifts down
;;; to index 0 (negative-diff shift runs low-to-high).
(let* ((m   (make-stub-map 'shift-contract))
       (fkey (make-keyremap m))
       (kb   (make-keybuf (char->integer #\a) (char->integer #\X))))
  ((%sym 'define-key) m (vector (char->integer #\a)) (vector))
  (check "m21/step/shift-contract/returns-diff"
         -1 (rks-keyremap-step! fkey kb 2 #t #nil))
  (check "m21/step/shift-contract/trailing" (char->integer #\X)
         (vector-ref kb 0)))

;;; --- 3.10 unbound-key reset path (review Finding 2) ------------------
;;; A key with no binding in the map takes the not-bound branch; since
;;; (get_keymap nil) is not a keymap, the scan resets with the
;;; order-sensitive C gotcha `fkey->end = ++fkey->start;`: start
;;; increments first, then end copies the new start.  The most common
;;; real case (most keys are not remapped), and the least tested before
;;; this check.
(let* ((m   (make-stub-map 'unbound-root))
       (fkey (make-keyremap m))
       (kb   (make-keybuf (char->integer #\a))))
  ;; make-stub-map binds only 'x', so 'a' is unbound.
  (check "m21/step/unbound/returns-false" #f
         (rks-keyremap-step! fkey kb 1 #t #nil))
  (check "m21/step/unbound/start-end-incremented"
         '(1 1) (list (keyremap-start fkey) (keyremap-end fkey)))
  (check "m21/step/unbound/map-restored" m (keyremap-map fkey)))

;;; Scheme mirror of the C --rks-walk-indec loop (src/keyboard.c:10228-10243).
;;; Drives rks-keyremap-step! until FKEY.end >= RKS-T, exactly like the C
;;; `while (indec.end < rks_t)` loop, with doit = true and
;;; input = max(rks_t, mock).  Returns (done? mock): done? is #t when a
;;; translation completed (mock = diff + max(rks_t, mock-in)); #f when
;;; the walk exhausted without translating (mock unchanged, as in C).
(define (scheme-walk-indec fkey keybuf rks-t mock prompt)
  (let loop ((mock mock))
    (if (>= (keyremap-end fkey) rks-t)
        (list #f mock)
        (let ((diff (rks-keyremap-step! fkey keybuf
                                        (max rks-t mock) #t prompt)))
          (if diff
              (list #t (+ diff (max rks-t mock)))
              (loop mock))))))

;;; --- 3.11 loop-level walk: compose steps like the C --rks-walk-indec
;;; A Scheme loop drives rks-keyremap-step! the way C --rks-walk-indec
;;; drives keyremap_step, so the composed walk — descend submap, then
;;; translate, then accumulate mock — is exercised end to end rather
;;; than one isolated step at a time.  (Live parity against the C DEFUN
;;; is deferred to imp-3; see the section-3 header comment.)
(let* ((m   (make-stub-map 'walk-root))
       (m2  (make-stub-map 'walk-child))
       (fkey (make-keyremap m))
       (kb   (make-keybuf (char->integer #\a) (char->integer #\b))))
  ((%sym 'define-key) m (vector (char->integer #\a)) m2)
  ((%sym 'define-key) m2 (vector (char->integer #\b))
        (vector (char->integer #\x) (char->integer #\y) (char->integer #\z)))
  ;; Walk keybuf [a b] with rks_t = 2, mock-in = 0:
  ;;   step 1: 'a' → submap m2 (descend; start=0, end=1, map=m2).
  ;;   step 2: 'b' → [x y z] (len 3); diff = 3 - (2 - 0) = 1.
  ;;   mock = 1 + max(2, 0) = 3.  Final keybuf [x y z], start=end=3.
  (let ((r (scheme-walk-indec fkey kb 2 0 #nil)))
    (check "m21/walk/indec/done" #t (car r))
    (check "m21/walk/indec/mock" 3 (cadr r))
    (check "m21/walk/indec/keybuf"
           (vector (char->integer #\x) (char->integer #\y)
                   (char->integer #\z))
           (front-vector kb 3))
    (check "m21/walk/indec/start-end" '(3 3)
           (list (keyremap-start fkey) (keyremap-end fkey)))))

;;; --- 3.12 loop-level walk: all-unbound keybuf exhausts the walk -----
;;; A keybuf with no binding in the map exhausts the walk without
;;; translating: the loop returns done=#f and leaves mock unchanged
;;; (mirroring the C loop reaching its end condition), and each step
;;; exercised the unbound reset path (3.10).
(let* ((m   (make-stub-map 'walk-unbound))
       (fkey (make-keyremap m))
       (kb   (make-keybuf (char->integer #\q))))
  (let ((r (scheme-walk-indec fkey kb 1 0 #nil)))
    (check "m21/walk/unbound/done" #f (car r))
    (check "m21/walk/unbound/mock-unchanged" 0 (cadr r))
    (check "m21/walk/unbound/start-end"
           '(1 1) (list (keyremap-start fkey) (keyremap-end fkey)))))
