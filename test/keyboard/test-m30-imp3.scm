;;; test-m30-imp3.scm --- M30 imp-3: plain fixnum cell conversion proof.
;;;
;;; brief.org (M30 imp-3) moves the plain fixnum cells to the cell table
;;; (src/keyboard.c cell_table) and deletes the per-cell setter DEFUNs.
;;; The Scheme accessor names stay, so the mod/ call sites do not change.
;;; They now live in (emacs cell-accessors).
;;;
;;; This corpus pins, for each converted cell:
;;;
;;;   * a write through the table and a read through the table;
;;;   * agreement between the table path and the named Scheme accessor;
;;;   * agreement between the table path and the stay-C getter (this
;;;     proves the table binds the same C cell);
;;;   * for raw_keybuf_count: a negative value signals (CHECK_FIXNAT);
;;;   * the converted names are still registered;
;;;   * the stay-C names are still registered;
;;;   * a missing name signals for --cell-ref and --cell-set!.
;;;
;;; Converted cells (table key <-> stay-C getter):
;;;   --set-down-mouse-line-number-width <-> --down-mouse-line-number-width
;;;   --set-last-mouse-button            <-> --last-mouse-button
;;;   --set-last-mouse-x                 <-> --last-mouse-x
;;;   --set-last-mouse-y                 <-> --last-mouse-y
;;;   --set-double-click-count           <-> --double-click-count
;;;   --set-menu-bar-items-index         <-> --menu-bar-items-index
;;;   --set-tab-bar-items-count          <-> --tab-bar-items-count
;;;   --set-tool-bar-items-count         <-> --tool-bar-items-count
;;;   --set-windows-or-buffers-changed   <-> (no getter exists)
;;;   --set-raw-keybuf-count             <-> --raw-keybuf-count
;;;
;;; Sourced by test-m30-imp3.el via eval-scheme.  Accumulates
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

;;; --- one plain fixnum cell: table path vs accessor vs stay-C getter --

(define (check-fixnum-cell label key getter)
  (let ((old (cell-ref key)))
    ;; 1. A write through the table and a read through the table.
    (cell-set! key 42)
    (check (string-append label "/table-set-table-read") 42 (cell-ref key))
    ;; 2. The named Scheme accessor agrees with the table path.
    ((subr key) 17)
    (check (string-append label "/accessor-agrees-table") 17 (cell-ref key))
    (check (string-append label "/accessor-agrees-getter") 17
           ((subr getter)))
    ;; 3. The table path and the stay-C getter bind the same C cell.
    ;;    A negative value is legal for a plain int cell.
    (cell-set! key -3)
    (check (string-append label "/table-agrees-getter-negative") -3
           ((subr getter)))
    (check (string-append label "/table-read-negative") -3 (cell-ref key))
    ;; Restore the first value.
    (cell-set! key old)))

(check-fixnum-cell "dmlnw" '--set-down-mouse-line-number-width
                   '--down-mouse-line-number-width)
(check-fixnum-cell "lmb" '--set-last-mouse-button '--last-mouse-button)
(check-fixnum-cell "lmx" '--set-last-mouse-x '--last-mouse-x)
(check-fixnum-cell "lmy" '--set-last-mouse-y '--last-mouse-y)
(check-fixnum-cell "dcc" '--set-double-click-count '--double-click-count)
(check-fixnum-cell "mbi" '--set-menu-bar-items-index '--menu-bar-items-index)
(check-fixnum-cell "tbi" '--set-tab-bar-items-count '--tab-bar-items-count)
(check-fixnum-cell "tlbi" '--set-tool-bar-items-count '--tool-bar-items-count)

;;; --- windows_or_buffers_changed: no stay-C getter -------------------

(let ((old (cell-ref '--set-windows-or-buffers-changed)))
  (cell-set! '--set-windows-or-buffers-changed 39)
  (check "wobc/table-set-table-read" 39 (cell-ref '--set-windows-or-buffers-changed))
  ((subr '--set-windows-or-buffers-changed) 21)
  (check "wobc/accessor-agrees-table" 21 (cell-ref '--set-windows-or-buffers-changed))
  (cell-set! '--set-windows-or-buffers-changed old))

;;; --- raw_keybuf_count: a fixnum count cell (CELL_FIXNAT) ------------

(let ((old (cell-ref '--set-raw-keybuf-count)))
  (cell-set! '--set-raw-keybuf-count 5)
  (check "rkbc/table-set-table-read" 5 (cell-ref '--set-raw-keybuf-count))
  ((subr '--set-raw-keybuf-count) 7)
  (check "rkbc/accessor-agrees-table" 7 (cell-ref '--set-raw-keybuf-count))
  (check "rkbc/table-agrees-getter" 7 ((subr '--raw-keybuf-count)))
  ;; A negative value must signal (the cell indexes raw_keybuf).
  (check "rkbc/negative-table-signals" #t
         (signals? (lambda () (cell-set! '--set-raw-keybuf-count -1))))
  (check "rkbc/negative-accessor-signals" #t
         (signals? (lambda () ((subr '--set-raw-keybuf-count) -1))))
  ;; The cell is unchanged after the rejected writes.
  (check "rkbc/value-kept-after-reject" 7 (cell-ref '--set-raw-keybuf-count))
  (cell-set! '--set-raw-keybuf-count old))

;;; --- a plain int cell still accepts a negative value ----------------

(check "fixnum-accepts-negative" -9
       (let ((old (cell-ref '--set-last-mouse-x)))
         (cell-set! '--set-last-mouse-x -9)
         (let ((v (cell-ref '--set-last-mouse-x)))
           (cell-set! '--set-last-mouse-x old)
           v)))

;;; --- CELL_FIXNUM keeps the CHECK_FIXNUM duty (cr.org F6/2) ----------
;;; A bignum must signal, as the deleted per-cell setter did.

(check "fixnum-rejects-bignum" #t
       (let ((old (cell-ref '--set-last-mouse-x)))
         (let ((r (signals? (lambda ()
                              (cell-set! '--set-last-mouse-x (expt 2 100))))))
           (check "fixnum-bignum-keeps-value" old
                  (cell-ref '--set-last-mouse-x))
           (cell-set! '--set-last-mouse-x old)
           r)))

(check "fixnum-accessor-rejects-bignum" #t
       (let ((old ((subr '--last-mouse-x))))
         (let ((r (signals? (lambda () ((subr '--set-last-mouse-x)
                                        (expt 2 100))))))
           (check "fixnum-bignum-accessor-keeps-value" old
                  ((subr '--last-mouse-x)))
           ((subr '--set-last-mouse-x) old)
           r)))

;;; --- the converted names are registered -----------------------------

(for-each
 (lambda (name)
   (check (string-append "registered:" (symbol->string name)) #t
          (truthy? (subr name))))
 '( --set-down-mouse-line-number-width
    --set-last-mouse-button
    --set-last-mouse-x
    --set-last-mouse-y
    --set-double-click-count
    --set-menu-bar-items-index
    --set-tab-bar-items-count
    --set-tool-bar-items-count
    --set-windows-or-buffers-changed
    --set-raw-keybuf-count))

;;; --- stay-C names remain --------------------------------------------

(for-each
 (lambda (name)
   (check (string-append "stay-c:" (symbol->string name)) #t
          (truthy? (subr name))))
 '( --down-mouse-line-number-width
    --last-mouse-button
    --last-mouse-x
    --last-mouse-y
    --double-click-count
    --menu-bar-items-index
    --tab-bar-items-count
    --tool-bar-items-count
    --raw-keybuf-count
    --set-button-down-time
    --set-this-command-key-count
    --set-this-single-command-key-start
    --set-force-quit-count!
    --set-ie-arg
    --set-ie-code
    --set-ie-modifiers
    --set-ie-frame-or-window
    --set-kboard-kbd-queue-has-data
    --set-buffer-from-selected-window))

;;; --- error path: a missing name must signal -------------------------

(check "error/ref-unknown-signals" #t
       (signals? (lambda () (cell-ref '--no-such-cell-m30-imp3))))
(check "error/set-unknown-signals" #t
       (signals? (lambda () (cell-set! '--no-such-cell-m30-imp3 1))))
