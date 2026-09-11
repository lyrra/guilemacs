;;; test-m30-imp4.scm --- M30 imp-4: plain Lisp_Object cell conversion proof.
;;;
;;; brief.org (M30 imp-4) moves the remaining plain Lisp_Object cells to
;;; the cell table (src/keyboard.c cell_table) and deletes the per-cell
;;; get/set DEFUNs.  The Scheme accessor names stay, so the mod/ call
;;; sites do not change.  They now live in (emacs cell-accessors).
;;;
;;; This corpus pins, for each converted cell:
;;;
;;;   * a write through the table and a read through the stay-C getter;
;;;   * a write through the named Scheme accessor and a read through the
;;;     table;
;;;   * the object survives a forced garbage collection between the
;;;     write and the read (the cell is a GC root) -- the imp-4 stress;
;;;   * the converted names are still registered;
;;;   * the stay-C names remain registered;
;;;   * --cell-ref on a stay-C name signals (it is not a table key);
;;;   * a missing name signals for --cell-ref and --cell-set!;
;;;   * the lookup memo accepts an uninterned symbol (cr.org F2).
;;;
;;; Converted cells (table key <-> stay-C getter):
;;;   --set-frame-relative-event-pos        <-> --frame-relative-event-pos
;;;   --set-menu-bar-items-vector           <-> --menu-bar-items-vector
;;;   --set-tab-bar-items-vector            <-> --tab-bar-items-vector
;;;   --set-tool-bar-items-vector           <-> --tool-bar-items-vector
;;;   --set-menu-bar-one-keymap-changed-items
;;;                                         <-> --menu-bar-one-keymap-changed-items
;;;   --set-menu-bar-touch-id               <-> --menu-bar-touch-id
;;;   --set-read-key-sequence-remapped       <-> --read-key-sequence-remapped
;;;   --set-internal-last-event-frame        <-> --get-internal-last-event-frame
;;;   --set-unread-switch-frame              <-> --get-unread-switch-frame
;;;
;;; Sourced by test-m30-imp4.el via eval-scheme.  Accumulates
;;; (NAME STATUS) pairs into test-results for readback from elisp.

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (subr name)
  (symbol-function name))

(define (truthy? x)
  (not (eq? x #nil)))

(define (cell-ref name)
  ((subr '--cell-ref) name))

(define (cell-set! name val)
  ((subr '--cell-set!) name val))

(define (signals? thunk)
  (catch #t
    (lambda () (thunk) #f)
    (lambda (k . args) #t)))

(define (force-gc)
  "Force a Lisp_Object garbage collection.  The C cell is a staticpro
root, so a stored object must survive this."
  ((subr 'garbage-collect)))

;;; --- one plain object cell: table path vs stay-C getter --------------

(define (check-object-cell label key getter)
  (let ((old (cell-ref key)))
    ;; 1. A write through the table, a read through the stay-C getter.
    (cell-set! key (list 'table-write label))
    (check (string-append label "/table-set-getter-read")
           (list 'table-write label) ((subr getter)))
    ;; 2. A write through the named Scheme accessor, a read through the
    ;;    table.  The deleted DEFUN was this same plain write.
    ((subr key) (list 'accessor-write label))
    (check (string-append label "/accessor-set-table-read")
           (list 'accessor-write label) (cell-ref key))
    ;; 3. GC stress: store a fresh object, force a garbage collection
    ;;    while only the C cell references it, then read it back through
    ;;    both paths.  A collected object would give a different value.
    (cell-set! key (list 'gc-stress label))
    (force-gc)
    (check (string-append label "/gc-stress-table-read")
           (list 'gc-stress label) (cell-ref key))
    (check (string-append label "/gc-stress-getter-read")
           (list 'gc-stress label) ((subr getter)))
    ;; Restore the first value.
    (cell-set! key old)))

(check-object-cell "fre" '--set-frame-relative-event-pos
                   '--frame-relative-event-pos)
(check-object-cell "mbi" '--set-menu-bar-items-vector
                   '--menu-bar-items-vector)
(check-object-cell "tbi" '--set-tab-bar-items-vector
                   '--tab-bar-items-vector)
(check-object-cell "tlbi" '--set-tool-bar-items-vector
                    '--tool-bar-items-vector)
(check-object-cell "mbok" '--set-menu-bar-one-keymap-changed-items
                   '--menu-bar-one-keymap-changed-items)
(check-object-cell "mbti" '--set-menu-bar-touch-id '--menu-bar-touch-id)
(check-object-cell "rksr" '--set-read-key-sequence-remapped
                   '--read-key-sequence-remapped)
(check-object-cell "ilef" '--set-internal-last-event-frame
                   '--get-internal-last-event-frame)
(check-object-cell "usf" '--set-unread-switch-frame
                   '--get-unread-switch-frame)

;;; --- a get/set pair shares one table row ----------------------------
;;; The read name --get-internal-last-event-frame is not a table key,
;;; but it reads the same cell as --set-internal-last-event-frame.

(check "pair/ilef-getter-agrees-table" #t
       (let ((old (cell-ref '--set-internal-last-event-frame)))
         (cell-set! '--set-internal-last-event-frame (list 'pair-ilef))
         (let ((r (equal? ((subr '--get-internal-last-event-frame))
                          (list 'pair-ilef))))
           (cell-set! '--set-internal-last-event-frame old)
           r)))

(check "pair/usf-getter-agrees-table" #t
       (let ((old (cell-ref '--set-unread-switch-frame)))
         (cell-set! '--set-unread-switch-frame (list 'pair-usf))
         (let ((r (equal? ((subr '--get-unread-switch-frame))
                          (list 'pair-usf))))
           (cell-set! '--set-unread-switch-frame old)
           r)))

;;; --- the converted names are registered -----------------------------

(for-each
 (lambda (name)
   (check (string-append "registered:" (symbol->string name)) #t
          (truthy? (subr name))))
 '( --set-frame-relative-event-pos
    --set-menu-bar-items-vector
    --set-tab-bar-items-vector
    --set-tool-bar-items-vector
    --set-menu-bar-one-keymap-changed-items
    --set-menu-bar-touch-id
    --set-read-key-sequence-remapped
    --set-internal-last-event-frame
    --set-unread-switch-frame
    --get-internal-last-event-frame
    --get-unread-switch-frame))

;;; --- stay-C names remain --------------------------------------------
;;; The bare C getters that lazy-init a vector or give an independent
;;; read stay C.  getctag stays C: no staticpro roots it.

(for-each
 (lambda (name)
   (check (string-append "stay-c:" (symbol->string name)) #t
          (truthy? (subr name))))
 '( --frame-relative-event-pos
    --menu-bar-items-vector
    --tab-bar-items-vector
    --tool-bar-items-vector
    --menu-bar-one-keymap-changed-items
    --menu-bar-touch-id
    --read-key-sequence-remapped
    --get-ctag
    --set-ctag))

;;; --- a stay-C name is not a table key -------------------------------

(for-each
 (lambda (name)
   (check (string-append "stay-c-not-in-table:" (symbol->string name)) #t
          (signals? (lambda () (cell-ref name)))))
 '( --frame-relative-event-pos
    --menu-bar-items-vector
    --tab-bar-items-vector
    --tool-bar-items-vector
    --menu-bar-one-keymap-changed-items
    --menu-bar-touch-id
    --read-key-sequence-remapped
    --get-ctag
    --set-ctag))

;;; --- the lookup memo accepts an uninterned symbol -------------------
;;; cr.org F2: lookup_cell caches the last name on the strcmp hit path,
;;; for any symbol.  An uninterned symbol (make-symbol) is not in the
;;; obarray.  last_cell_name is a staticpro root, so the memo may hold
;;; it.  A fresh uninterned symbol with a table-key name must read the
;;; same cell as the interned key.

(check "memo/uninterned-symbol-reads-cell" #t
       (let* ((key '--set-menu-bar-touch-id)
              (old (cell-ref key))
              (fresh (make-symbol "--set-menu-bar-touch-id")))
         ;; The first call caches the uninterned symbol in the memo.
         (cell-set! key (list 'memo-uniq))
         (let ((first (equal? (cell-ref fresh) (list 'memo-uniq))))
           ;; Force a GC.  The root keeps the cached symbol alive.
           (force-gc)
           ;; A second call must reuse the memo without a false hit.
           (let ((second (equal? (cell-ref fresh) (list 'memo-uniq))))
             (cell-set! key old)
             (and first second)))))

;;; --- a different name evicts the one-entry memo ---------------------

(check "memo/name-change-evicts" #t
       (let ((a '--set-menu-bar-touch-id)
             (b '--set-unread-switch-frame))
         (let ((oa (cell-ref a)) (ob (cell-ref b)))
           (cell-set! a (list 'memo-a))
           (cell-set! b (list 'memo-b))
           (let ((ra (equal? (cell-ref a) (list 'memo-a)))
                 (rb (equal? (cell-ref b) (list 'memo-b)))
                 (ra2 (equal? (cell-ref a) (list 'memo-a))))
             (cell-set! a oa)
             (cell-set! b ob)
             (and ra rb ra2)))))

;;; --- error path: a missing name must signal -------------------------

(check "error/ref-unknown-signals" #t
       (signals? (lambda () (cell-ref '--no-such-cell-m30-imp4))))
(check "error/set-unknown-signals" #t
       (signals? (lambda () (cell-set! '--no-such-cell-m30-imp4 1))))
