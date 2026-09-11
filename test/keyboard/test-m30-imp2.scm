;;; test-m30-imp2.scm --- M30 imp-2: plain bool cell conversion proof.
;;;
;;; brief.org (M30 imp-2) moves the plain bool cells to the cell table
;;; (src/keyboard.c cell_table) and deletes the per-cell DEFUNs.  The
;;; Scheme accessor names stay, so the mod/ call sites do not change.
;;; They now live in (emacs cell-accessors) and resolve the name in the
;;; elisp function slot.
;;;
;;; This corpus pins, for each converted bool cell:
;;;
;;;   * a write through the table and a read through the table;
;;;   * agreement between the table path and the Scheme accessor path;
;;;   * the !NILP convert (a non-nil, non-#t value gives true);
;;;   * a missing name still signals;
;;;   * the converted names are still registered.
;;;
;;; Converted cells:
;;;   echoing                     <-> --set-echoing! / --echoing-p
;;;   ignore_mouse_drag_p         <-> --set-ignore-mouse-drag-p /
;;;                                   --clear-ignore-mouse-drag
;;;   display_working_on_window_p <-> --clear-display-working-on-window-p
;;;
;;; waiting_for_input is NOT converted: it is a per-thread field
;;; (src/thread.h), so no table entry exists.  The corpus pins that its
;;; C subrs remain.
;;;
;;; Sourced by test-m30-imp2.el via eval-scheme.  Accumulates
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

;;; --- echoing: --set-echoing! / --echoing-p --------------------------

(let ((old (cell-ref '--set-echoing!)))
  ;; The Scheme accessor writes t; the table reads t.
  ((subr '--set-echoing!) #t)
  (check "echoing/accessor-set-table-read-t" #t
         (truthy? (cell-ref '--set-echoing!)))
  ;; The table and the Scheme getter agree.
  (check "echoing/table-agrees-accessor-t" #t
         (eq? (truthy? (cell-ref '--set-echoing!))
              (truthy? ((subr '--echoing-p)))))
  ;; The table writes nil; the Scheme getter reads nil.
  (cell-set! '--set-echoing! #nil)
  (check "echoing/table-set-accessor-read-nil" #nil
         ((subr '--echoing-p)))
  ;; The Scheme accessor clears; the table reads nil.
  ((subr '--set-echoing!) #nil)
  (check "echoing/accessor-clear-table-read-nil" #nil
         (cell-ref '--set-echoing!))
  ;; !NILP: a non-nil, non-#t value (fixnum 0) converts to true.
  (cell-set! '--set-echoing! 0)
  (check "echoing/non-nil-0-converts-true" #t
         (truthy? ((subr '--echoing-p))))
  ;; Restore.
  ((subr '--set-echoing!) old))

;;; --- ignore_mouse_drag_p: --set-ignore-mouse-drag-p ----------------

;; The C getter --ignore-mouse-drag-p stays C (not in the delete set),
;; so it gives an independent read of the same cell.
(let ((old (cell-ref '--set-ignore-mouse-drag-p)))
  ;; Table and the C getter agree on the first value.
  (check "imd/table-agrees-c-getter" #t
         (eq? (truthy? (cell-ref '--set-ignore-mouse-drag-p))
              (truthy? ((subr '--ignore-mouse-drag-p)))))
  ;; The Scheme accessor writes t; the table reads t.
  ((subr '--set-ignore-mouse-drag-p) #t)
  (check "imd/accessor-set-table-read-t" #t
         (truthy? (cell-ref '--set-ignore-mouse-drag-p)))
  ;; The Scheme clear writes nil; the table reads nil.
  ((subr '--clear-ignore-mouse-drag))
  (check "imd/accessor-clear-table-read-nil" #nil
         (cell-ref '--set-ignore-mouse-drag-p))
  ;; The table writes t; the C getter sees t.
  (cell-set! '--set-ignore-mouse-drag-p #t)
  (check "imd/table-set-c-getter-t" #t
         (truthy? ((subr '--ignore-mouse-drag-p))))
  ;; !NILP: a non-nil value converts to true.
  (cell-set! '--set-ignore-mouse-drag-p 0)
  (check "imd/non-nil-0-converts-true" #t
         (truthy? (cell-ref '--set-ignore-mouse-drag-p)))
  ;; Restore.
  (cell-set! '--set-ignore-mouse-drag-p old))

;;; --- display_working_on_window_p ------------------------------------
;;;
;;; No getter exists, so the round-trip is checked through the table.

(let ((old (cell-ref '--clear-display-working-on-window-p)))
  (cell-set! '--clear-display-working-on-window-p #t)
  (check "dwwp/table-set-table-read-t" #t
         (truthy? (cell-ref '--clear-display-working-on-window-p)))
  ((subr '--clear-display-working-on-window-p))
  (check "dwwp/accessor-clear-table-read-nil" #nil
         (cell-ref '--clear-display-working-on-window-p))
  ;; The operation DEFUN --reset-redisplay-tick-state also clears this
  ;; cell; it stays C and must remain registered.
  (check "dwwp/reset-op-still-registered" #t
         (truthy? (subr '--reset-redisplay-tick-state)))
  (cell-set! '--clear-display-working-on-window-p old))

;;; --- the converted names are registered -----------------------------

(check "registered:--set-echoing!" #t (truthy? (subr '--set-echoing!)))
(check "registered:--echoing-p" #t (truthy? (subr '--echoing-p)))
(check "registered:--set-ignore-mouse-drag-p" #t
       (truthy? (subr '--set-ignore-mouse-drag-p)))
(check "registered:--clear-ignore-mouse-drag" #t
       (truthy? (subr '--clear-ignore-mouse-drag)))
(check "registered:--clear-display-working-on-window-p" #t
       (truthy? (subr '--clear-display-working-on-window-p)))

;;; --- stay-C: waiting_for_input subrs remain -------------------------

(check "stay-c:--clear-waiting-for-input" #t
       (truthy? (subr '--clear-waiting-for-input)))
(check "stay-c:--waiting-for-input-p" #t
       (truthy? (subr '--waiting-for-input-p)))

;;; --- error path: a missing name must signal -------------------------

(check "error/ref-unknown-signals" #t
       (signals? (lambda () (cell-ref '--no-such-cell-m30-imp2))))
(check "error/set-unknown-signals" #t
       (signals? (lambda () (cell-set! '--no-such-cell-m30-imp2 1))))
