;;; test-m30-imp1.scm --- M30 imp-1: table-driven cell subr proof.
;;;
;;; brief.org (M30 imp-1) adds one C table of cells plus two subrs:
;;; --cell-ref reads a cell, --cell-set! writes a cell.  The entry kind
;;; picks the convert step: boolean, fixnum, or Lisp_Object.  This
;;; commit keeps all 74 per-cell DEFUNs, so both paths stay live and
;;; can be compared.
;;;
;;; This corpus pins that the two paths agree, one cell per kind:
;;;
;;;   * bool    --set-echoing!              -> &echoing
;;;   * fixnum  --set-raw-keybuf-count      -> &raw_keybuf_count
;;;   * object  --set-frame-relative-event-pos -> &frame_relative_event_pos
;;;     (already rooted by staticpro in syms_of_keyboard)
;;;
;;; Each case sets a cell one way and reads it the other way, then
;;; restores the first value.  A missing name must signal, never return
;;; a default.
;;;
;;; Sourced by test-m30-imp1.el via eval-scheme.  Accumulates
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

;;; --- bool cell: --set-echoing! -> &echoing --------------------------
;;;
;;; The old getter is --echoing-p (src/keyboard.c, added M26).  Compare
;;; the table path against both the old setter and the old getter.

(let ((old (cell-ref '--set-echoing!)))
  ;; The old DEFUN writes t; the table reads t.
  ((subr '--set-echoing!) #t)
  (check "bool/old-set-table-read-t" #t
         (truthy? (cell-ref '--set-echoing!)))
  ;; The table and the old getter --echoing-p agree on t.
  (check "bool/table-agrees-old-get-t" #t
         (eq? (truthy? (cell-ref '--set-echoing!))
              (truthy? ((subr '--echoing-p)))))
  ;; The table writes nil; the table reads nil.
  (cell-set! '--set-echoing! #nil)
  (check "bool/table-set-table-read-nil" #nil
         (cell-ref '--set-echoing!))
  ;; The old getter sees the table write (nil), and agrees with the table.
  (check "bool/table-agrees-old-get-nil" #t
         (eq? (truthy? (cell-ref '--set-echoing!))
              (truthy? ((subr '--echoing-p)))))
  (check "bool/table-set-old-get-nil" #nil
         ((subr '--echoing-p)))
  ;; The table writes t; the table reads t.
  (cell-set! '--set-echoing! #t)
  (check "bool/table-set-table-read-t" #t
         (truthy? (cell-ref '--set-echoing!)))
  ;; Restore the first value through the old DEFUN.
  ((subr '--set-echoing!) old))

;;; --- fixnum cell: --set-raw-keybuf-count -> &raw_keybuf_count -------

(let ((old ((subr '--raw-keybuf-count))))
  ;; Set n through the old DEFUN; read n through the table.
  ((subr '--set-raw-keybuf-count) 1)
  (check "fixnum/old-set-table-read" 1
         (cell-ref '--set-raw-keybuf-count))
  ;; The old getter and the table agree.
  (check "fixnum/old-get-agrees"
         ((subr '--raw-keybuf-count))
         (cell-ref '--set-raw-keybuf-count))
  ;; Set m through the table; read m through the table.
  (cell-set! '--set-raw-keybuf-count 2)
  (check "fixnum/table-set-table-read" 2
         (cell-ref '--set-raw-keybuf-count))
  ;; The old getter sees the table write.
  (check "fixnum/table-set-old-get" 2
         ((subr '--raw-keybuf-count)))
  ;; Restore the first value through the old DEFUN.
  ((subr '--set-raw-keybuf-count) old))

;;; --- object cell: --set-frame-relative-event-pos --------------------

(let ((old ((subr '--frame-relative-event-pos)))
      (new (cons 111 222)))
  ;; The table and the old getter agree on the old value.
  (check "object/old-get-agrees" old
         (cell-ref '--set-frame-relative-event-pos))
  ;; Write a new value through the table; the old getter sees it.
  (cell-set! '--set-frame-relative-event-pos new)
  (check "object/table-set-old-get" new
         ((subr '--frame-relative-event-pos)))
  ;; The table reads the new value back.
  (check "object/table-set-table-read" new
         (cell-ref '--set-frame-relative-event-pos))
  ;; Restore the old value.
  (cell-set! '--set-frame-relative-event-pos old)
  (check "object/restore" old
         ((subr '--frame-relative-event-pos))))

;;; --- error path: a missing name must signal, not return a default ---

(check "error/ref-unknown-signals" #t
       (catch #t
         (lambda ()
           (cell-ref '--no-such-cell-m30)
           #f)
         (lambda (k . args) #t)))

(check "error/set-unknown-signals" #t
       (catch #t
         (lambda ()
           (cell-set! '--no-such-cell-m30 1)
           #f)
         (lambda (k . args) #t)))

;;; --- table registration: the two subrs exist ------------------------

(check "registered:--cell-ref" #t
       (truthy? (subr '--cell-ref)))
(check "registered:--cell-set!" #t
       (truthy? (subr '--cell-set!)))
