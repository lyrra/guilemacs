;;; test-m28-imp4.scm --- M28 imp-4, Step 1: port of the generic
;;; <rks-state> record primitives.
;;;
;;; brief.org (M28 imp-4) Step 1 removes the five thin slot-index
;;; DEFUNs (--rks-record-get-int / --rks-record-set-int /
;;; --rks-record-get / --rks-record-set / --rks-record-set-bool) and
;;; rewrites rks-sync-read / rks-sync-write in (emacs
;;; read-key-sequence) to move fields with the srfi-9 field accessors
;;; directly.  The record becomes the read source for the synced
;;; scalars (key-count, mock-input, current-binding, first-unbound,
;;; shift-translated).
;;;
;;; This corpus asserts the Step-1 deliverable that does NOT need the
;;; performance harness:
;;;
;;;   - the five --rks-record-* names no longer register;
;;;   - rks-sync-read / rks-sync-write still exist and move a field
;;;     record <-> C file-static in both directions (the accessor
;;;     rewrite preserved the round-trip semantics);
;;;   - the <rks-state> record slots round-trip through the @@ idiom.
;;;
;;; NOTE: this is the Step-1 sub-slice of imp-4.  Bucket-A pairs,
;;; bucket-C (keyremap sync) and the bench remain (recorded in
;;; docs/kb.org); a later commit extends this corpus when they land.
;;;
;;; Same harness as test-m28-imp3.scm: Sourced by the .el wrapper via
;;; eval-scheme; accumulates (NAME STATUS) pairs into test-results for
;;; readback from elisp.

(use-modules (emacs read-key-sequence))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (%sym name)
  (symbol-function name))

(define-syntax-rule (@@rk sym)
  (@@ (emacs read-key-sequence) sym))

;; Explicit accessor names (srfi-9 auto-generated, not first-class in
;; elisp but fine from Scheme):
(define rks-state-key-count       (@@rk rks-state-key-count))
(define set-rks-state-key-count!  (@@rk set-rks-state-key-count!))
(define rks-state-mock-input      (@@rk rks-state-mock-input))
(define set-rks-state-mock-input! (@@rk set-rks-state-mock-input!))
(define rks-state-current-binding (@@rk rks-state-current-binding))
(define set-rks-state-current-binding!
  (@@rk set-rks-state-current-binding!))
(define rks-state-first-unbound   (@@rk rks-state-first-unbound))
(define set-rks-state-first-unbound! (@@rk set-rks-state-first-unbound!))
(define rks-state-shift-translated (@@rk rks-state-shift-translated))
(define set-rks-state-shift-translated!
  (@@rk set-rks-state-shift-translated!))
(define rks-state-new-binding     (@@rk rks-state-new-binding))
(define set-rks-state-new-binding! (@@rk set-rks-state-new-binding!))
(define rks-state-original-uppercase (@@rk rks-state-original-uppercase))
(define set-rks-state-original-uppercase!
  (@@rk set-rks-state-original-uppercase!))
(define rks-state-original-uppercase-position
  (@@rk rks-state-original-uppercase-position))
(define set-rks-state-original-uppercase-position!
  (@@rk set-rks-state-original-uppercase-position!))

(define make-rks-state            (@@rk make-rks-state))
(define rks-sync-read             (@@rk rks-sync-read))
(define rks-sync-write            (@@rk rks-sync-write))

;;; --- 0. The five record primitives are removed ----------------------
;; Step 1 deletes the DEFUNs; each name must now read back as nil
;; (same convention as test-m28-imp1.scm §1).
(for-each
 (lambda (name)
   (let ((sym (intern name)))
     (check (string-append "imp4/s1/no-defun/" name)
            #t
            (eq? (%sym sym) #nil))))
 '("--rks-record-get-int"
   "--rks-record-set-int"
   "--rks-record-get"
   "--rks-record-set"
   "--rks-record-set-bool"))

;; The state-stack trio that the sync helpers rely on still resolves.
(check "imp4/s1/state-current-exists" #t
       (not (eq? (%sym '--rks-state-current) #nil)))

;;; --- 1. Record slot accessors round-trip (the @@ idiom) -------------
(let ((s (make-rks-state)))
  (set-rks-state-key-count! s 7)
  (check "imp4/s1/record/key-count" 7 (rks-state-key-count s))
  (set-rks-state-mock-input! s 3)
  (check "imp4/s1/record/mock-input" 3 (rks-state-mock-input s))
  (set-rks-state-first-unbound! s 30)
  (check "imp4/s1/record/first-unbound" 30 (rks-state-first-unbound s))
  (set-rks-state-shift-translated! s #t)
  (check "imp4/s1/record/shift-translated" #t
         (rks-state-shift-translated s)))

;;; --- 2. rks-sync-read copies record -> C file-static ----------------
;; After the rewrite each branch still drives the C file-static mirror
;; from the record slot.  We read the mirror back through the surviving
;; bucket-B getter shims.  Only the bucket-B scalars (key-count ->
;; rks_t, mock-input -> rks_mock_input, current-binding ->
;; rks_current_binding) have a C file-static mirror; the bucket-A slots
;; (first-unbound, shift-translated) are record->record round-trips
;; (static retired) that Step 2 collapses, so they have no mirror to
;; read back here.
(let* ((s (make-rks-state))
       (sync rks-sync-read))
  ;; key-count -> rks_t (--rks-t, bucket B, stays C)
  (set-rks-state-key-count! s 5)
  (sync s 'key-count)
  (check "imp4/s1/read/key-count-to-rks-t" 5 ((%sym '--rks-t)))
  ;; mock-input -> rks_mock_input (--rks-mock-input, bucket B, stays C)
  (set-rks-state-mock-input! s 2)
  (sync s 'mock-input)
  (check "imp4/s1/read/mock-input" 2 ((%sym '--rks-mock-input)))
  ;; current-binding -> rks_current_binding (--rks-current-binding,
  ;; bucket B, stays C)
  (set-rks-state-current-binding! s (string->symbol "imp4-s1-cb"))
  (sync s 'current-binding)
  (check "imp4/s1/read/current-binding"
         (string->symbol "imp4-s1-cb") ((%sym '--rks-current-binding))))

;;; --- 3. rks-sync-write copies C file-static -> record ---------------
;; Set the mirror via its bucket-B setter, then sync it back into the
;; record.
(let* ((s (make-rks-state))
       (sync rks-sync-write))
  ;; rks_t -> key-count
  ((%sym '--set-rks-t) 9)
  (sync s 'key-count)
  (check "imp4/s1/write/key-count-from-rks-t" 9 (rks-state-key-count s))
  ;; rks_mock_input -> mock-input
  ((%sym '--set-rks-mock-input) 4)
  (sync s 'mock-input)
  (check "imp4/s1/write/mock-input" 4 (rks-state-mock-input s))
  ;; rks_current_binding -> current-binding
  ((%sym '--set-rks-current-binding) (string->symbol "imp4-s1-cb2"))
  (sync s 'current-binding)
  (check "imp4/s1/write/current-binding"
         (string->symbol "imp4-s1-cb2") (rks-state-current-binding s)))

;;; --- 4. Round-trip: record -> static -> record keeps the value ------
(let* ((s (make-rks-state))
       (rd rks-sync-read)
       (wr rks-sync-write))
  (set-rks-state-key-count! s 42)
  (rd s 'key-count)                    ; record -> static
  (set-rks-state-key-count! s 0)       ; clobber the slot
  (wr s 'key-count)                    ; static -> record
  (check "imp4/s1/roundtrip/key-count" 42 (rks-state-key-count s)))

;;; --- 5. shift-translated sync-write branch (cr.org F3) ---------------
;; cr.org F3: rks-sync-write's 'shift-translated branch (rewritten in
;; Step 1 from the slot-index bool setter to the typed accessor plus the
;; #t/#nil coercion) had no test.  The C getter it reads has no real
;; file-static mirror — it returns the ACTIVE <rks-state>'s
;; shift-translated (nil at depth 0).  Drive the branch by pushing a
;; source record whose shift-translated is #t, sync-writing into an
;; unrelated target, then popping.  dynamic-wind keeps the state stack
;; balanced even on a non-local exit.
(let* ((push   (%sym '--rks-state-stack-push))
       (pop    (%sym '--rks-state-stack-pop))
       (target (make-rks-state))
       (src    (make-rks-state)))
  (set-rks-state-shift-translated! src #t)
  (dynamic-wind
    (lambda () (push src))
    (lambda () (rks-sync-write target 'shift-translated))
    (lambda () (pop)))
  ;; target starts unset (nil default); the branch must have copied the
  ;; active record's #t through the typed accessor.
  (check "imp4/s1/write/shift-translated-from-active" #t
         (rks-state-shift-translated target)))

;;; --- 6. Step 2 (bucket-A DELETE set): the 10 shim DEFUNs are gone --
;; brief.org Step 2 deletes these getter+setter pairs; after a rebuild
;; each name must read back as nil (same convention as §0 above).
(for-each
 (lambda (name)
   (let ((sym (intern name)))
     (check (string-append "imp4/s2/no-defun/" name)
            #t
            (eq? (%sym sym) #nil))))
 '("--rks-shift-translated-p"
   "--set-rks-shift-translated"
   "--rks-new-binding"
   "--set-rks-new-binding"
   "--rks-first-unbound"
   "--set-rks-first-unbound"
   "--rks-original-uppercase"
   "--set-rks-original-uppercase"
   "--rks-original-uppercase-position"
   "--set-rks-original-uppercase-position"))

;;; --- 7. Step 2: each bucket-A slot round-trips on a live record ----
;; brief.org Step 2: the 5 record slots are the single source of truth;
;; each must round-trip through its srfi-9 accessor on a live record.
(let ((s (make-rks-state)))
  (set-rks-state-new-binding! s (string->symbol "imp4-s2-nb"))
  (check "imp4/s2/record/new-binding" (string->symbol "imp4-s2-nb")
         (rks-state-new-binding s))
  (set-rks-state-first-unbound! s 7)
  (check "imp4/s2/record/first-unbound" 7 (rks-state-first-unbound s))
  (set-rks-state-original-uppercase! s (string->symbol "imp4-s2-ou"))
  (check "imp4/s2/record/original-uppercase"
         (string->symbol "imp4-s2-ou") (rks-state-original-uppercase s))
  (set-rks-state-original-uppercase-position! s 9)
  (check "imp4/s2/record/original-uppercase-position" 9
         (rks-state-original-uppercase-position s))
  (set-rks-state-shift-translated! s #t)
  (check "imp4/s2/record/shift-translated" #t
         (rks-state-shift-translated s)))

;;; --- 8. Step 2: first-unbound sync-write meaning is preserved -------
;; Mirror §5 for first-unbound: with an active source record pushed,
;; rks-sync-write 'first-unbound copies its value into an unrelated
;; target through the accessor (the branch survives Step 2).
(let* ((push   (%sym '--rks-state-stack-push))
       (pop    (%sym '--rks-state-stack-pop))
       (target (make-rks-state))
       (src    (make-rks-state)))
  (set-rks-state-first-unbound! src 12)
  (dynamic-wind
    (lambda () (push src))
    (lambda () (rks-sync-write target 'first-unbound))
    (lambda () (pop)))
  (check "imp4/s2/write/first-unbound-from-active" 12
         (rks-state-first-unbound target)))

;;; --- 9. Step 2: live-record accessor reads the pushed record --------
;; The Generation-B helpers now read/write the bucket-A slots through
;; the depth-0-safe live-record helpers.  With a record pushed, the
;; helper must read that record's slot (not a default).
(let* ((push (%sym '--rks-state-stack-push))
       (pop  (%sym '--rks-state-stack-pop))
       (src  (make-rks-state))
       (live-fu (@@rk rks-live-first-unbound)))
  (set-rks-state-first-unbound! src 21)
  (dynamic-wind
    (lambda () (push src))
    (lambda ()
      (check "imp4/s2/live/first-unbound-from-pushed" 21 (live-fu)))
    (lambda () (pop))))

;;; --- 10. Step 3 (bucket-C keyremap): the 15 shims are gone -----------
;; brief.org Step 3 deletes the 6 start/end getter+setter pairs and the
;; 3 bulk shims (--rks-keyremaps-shrink-by / --rks-reset-fkey-and-keytran-scans /
;; --rks-init-keyremaps).  After a rebuild each name reads back as nil
;; (same convention as §0 / §6 above).
(for-each
 (lambda (name)
   (let ((sym (intern name)))
     (check (string-append "imp4/s3/no-defun/" name)
            #t
            (eq? (%sym sym) #nil))))
 '("--rks-fkey-start"   "--rks-fkey-end"
   "--rks-keytran-start" "--rks-keytran-end"
   "--rks-indec-start"   "--rks-indec-end"
   "--set-rks-fkey-start" "--set-rks-fkey-end"
   "--set-rks-keytran-start" "--set-rks-keytran-end"
   "--set-rks-indec-start" "--set-rks-indec-end"
   "--rks-keyremaps-shrink-by"
   "--rks-reset-fkey-and-keytran-scans"
   "--rks-init-keyremaps"))

;; --- 11. Step 3: bucket-C live helpers on a pushed record ------------
;; The keyremap start/end fields are now read/written through srfi-9
;; accessors on the *live* <rks-state>.  We reach the unexported
;; accessors / helpers with the @@ idiom (as above).  Drive each helper
;; on a pushed record and check the depth-0 default separately.
(define rks-live-keytran-start      (@@rk rks-live-keytran-start))
(define rks-keyremaps-shrink-by!    (@@rk rks-keyremaps-shrink-by!))
(define rks-reset-fkey-and-keytran-scans!
  (@@rk rks-reset-fkey-and-keytran-scans!))
(define rks-state-fkey              (@@rk rks-state-fkey))
(define rks-state-keytran           (@@rk rks-state-keytran))
(define rks-state-indec             (@@rk rks-state-indec))
(define keyremap-rebase!            (@@rk keyremap-rebase!))
(define keyremap-start              (@@rk keyremap-start))
(define keyremap-end                (@@rk keyremap-end))
(define keyremap-map                (@@rk keyremap-map))
(define keyremap-parent             (@@rk keyremap-parent))
(define set-keyremap-map!           (@@rk set-keyremap-map!))
(define set-keyremap-start!         (@@rk set-keyremap-start!))
(define set-keyremap-end!           (@@rk set-keyremap-end!))

;; depth-0 default: no record pushed → rks-live-keytran-start = 0.
(check "imp4/s3/live/keytran-start-depth0-zero"
       0 (rks-live-keytran-start))

(define (sparse-map sym)
  (let ((m ((%sym 'make-sparse-keymap))))
    ((%sym 'define-key) m (vector (char->integer #\x)) sym)
    m))

;; shrink-by! decrements start, sets end = new start, map = parent, for
;; all three keyremaps on the pushed record.
(let* ((push   (%sym '--rks-state-stack-push))
       (pop    (%sym '--rks-state-stack-pop))
       (state  (make-rks-state))
       (fkey   (rks-state-fkey state))
       (keytran (rks-state-keytran state))
       (indec   (rks-state-indec state)))
  (keyremap-rebase! fkey    (sparse-map 's3-fkey))
  (keyremap-rebase! keytran (sparse-map 's3-keytran))
  (keyremap-rebase! indec   (sparse-map 's3-indec))
  ;; Seed nonzero scan starts and a non-parent map so the decrement and
  ;; the map=parent reset are each observable.
  (set-keyremap-start! fkey 10)
  (set-keyremap-start! keytran 20)
  (set-keyremap-start! indec 30)
  (set-keyremap-map! fkey (sparse-map 's3-fkey-m2))
  (set-keyremap-map! keytran (sparse-map 's3-keytran-m2))
  (set-keyremap-map! indec (sparse-map 's3-indec-m2))
  (let ((fkey-parent (keyremap-parent fkey)))
    (dynamic-wind
      (lambda () (push state))
      (lambda ()
        (rks-keyremaps-shrink-by! 2)
        (check "imp4/s3/shrink/fkey-start" 8 (keyremap-start fkey))
        (check "imp4/s3/shrink/fkey-end-eq-start" 8 (keyremap-end fkey))
        (check "imp4/s3/shrink/fkey-map-eq-parent" #t
               (eq? fkey-parent (keyremap-map fkey)))
        (check "imp4/s3/shrink/keytran-start" 18 (keyremap-start keytran))
        (check "imp4/s3/shrink/keytran-end-eq-start" 18 (keyremap-end keytran))
        (check "imp4/s3/shrink/keytran-map-eq-parent" #t
               (eq? (keyremap-parent keytran) (keyremap-map keytran)))
        (check "imp4/s3/shrink/indec-start" 28 (keyremap-start indec))
        (check "imp4/s3/shrink/indec-end-eq-start" 28 (keyremap-end indec))
        (check "imp4/s3/shrink/indec-map-eq-parent" #t
               (eq? (keyremap-parent indec) (keyremap-map indec))))
      (lambda () (pop)))))

;; reset-fkey-and-keytran-scans! zeroes start/end of fkey and keytran
;; ONLY — indec untouched, and map is NOT reset to parent.
(let* ((push   (%sym '--rks-state-stack-push))
       (pop    (%sym '--rks-state-stack-pop))
       (state  (make-rks-state))
       (fkey   (rks-state-fkey state))
       (keytran (rks-state-keytran state))
       (indec   (rks-state-indec state)))
  (keyremap-rebase! fkey    (sparse-map 's3-fkey))
  (keyremap-rebase! keytran (sparse-map 's3-keytran))
  (keyremap-rebase! indec   (sparse-map 's3-indec))
  ;; Pre-seed nonzero scans and a non-parent map so the reset's effect is
  ;; distinguishable from keyremap-reset! (which also sets map = parent).
  (set-keyremap-start! fkey 3)
  (set-keyremap-end!   fkey 5)
  (set-keyremap-start! keytran 7)
  (set-keyremap-end!   keytran 9)
  (set-keyremap-start! indec 11)      ; reset must NOT touch indec
  (set-keyremap-map! fkey (sparse-map 's3-fkey-m2))
  (let ((fkey-m2 (keyremap-map fkey))) ; remember the non-parent map
    (dynamic-wind
      (lambda () (push state))
      (lambda ()
        (rks-reset-fkey-and-keytran-scans!)
        (check "imp4/s3/reset/fkey-start-zero" 0 (keyremap-start fkey))
        (check "imp4/s3/reset/fkey-end-zero" 0 (keyremap-end fkey))
        (check "imp4/s3/reset/keytran-start-zero" 0 (keyremap-start keytran))
        (check "imp4/s3/reset/keytran-end-zero" 0 (keyremap-end keytran))
        ;; indec is untouched by the reset.
        (check "imp4/s3/reset/indec-start-unchanged" 11 (keyremap-start indec))
        ;; map is preserved (NOT reset to parent).
        (check "imp4/s3/reset/fkey-map-preserved" #t
               (eq? fkey-m2 (keyremap-map fkey))))
      (lambda () (pop)))))
