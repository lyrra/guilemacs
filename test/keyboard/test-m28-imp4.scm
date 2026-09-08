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
