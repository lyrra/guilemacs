;;; test-m19-tables.scm --- M19 imp-4: surviving key-name tables remain readable
;;;
;;; M19 imp-4 deletes two dead static tables from src/keyboard.c
;;; (lispy_kana_keys, lispy_drag_n_drop_names) and folds the
;;; lispy_wheel_names length into a literal.  The five accessor-backed
;;; tables (accent codes/keys, function keys, iso function keys,
;;; multimedia keys) stay in C.  This corpus proves those five tables
;;; are still readable through their DEFUNs, and that the wheel_syms
;;; cache (MES_CACHE_WHEEL, cache id 3) is still sized 4 after the
;;; literal swap.
;;;
;;; The expected f1/f35/delete vector slots come from the C table:
;;; FUNCTION_KEY_OFFSET is 0xff00, and f1/f35/delete sit at keysyms
;;; 0xffbe/0xffe0/0xffff, i.e. vector slots 190/224/255 on X builds.
;;; These slot checks are X-only; an NTGUI/Android build (offset 0)
;;; would index the vector differently.  The multimedia vector is
;;; empty on non-NTGUI builds (the DEFUN returns an empty vector when
;;; MULTIMEDIA_KEY_EVENT can't fire).
;;;
;;; The accessor DEFUNs are elisp functions in the runtime, so they are
;;; reached via symbol-function (the same path test-m19-fixes.scm uses
;;; for C primitives) rather than through module exports, which would
;;; expose private (emacs lispy-event) bindings.
;;;
;;; Sourced by test/keyboard/test-m19-tables.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results`.

(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

;; Call an elisp DEFUN by name, e.g. (%call '--lispy-accent-codes).
(define (%call name . args)
  (apply (symbol-function name) args))

(define (accent-codes)  (%call '--lispy-accent-codes))
(define (accent-keys)   (%call '--lispy-accent-keys))
(define (function-keys) (%call '--lispy-function-keys))
(define (iso-fk)        (%call '--iso-lispy-function-keys))
(define (mm-keys)       (%call '--lispy-multimedia-keys))
(define (wheel-cache)   (%call '--mes-cache-get 3))

;;; --- Case 1: accent codes and keys are non-empty vectors of equal
;;; length.
(let ((codes (accent-codes))
      (keys (accent-keys)))
  (report "accent/vectors"
          (if (and (vector? codes) (vector? keys)
                   (> (vector-length codes) 0)
                   (> (vector-length keys) 0))
              'PASS
              (list 'FAIL 'codes (and (vector? codes) (vector-length codes))
                    'keys (and (vector? keys) (vector-length keys)))))
  (report "accent/equal-length"
          (if (= (vector-length codes) (vector-length keys))
              'PASS
              (list 'FAIL 'codes (vector-length codes)
                    'keys (vector-length keys)))))

;;; --- Case 2: function-keys contains "f1", "f35", "delete" at their
;;; known slots (0xffbe/0xffe0/0xffff minus 0xff00).
(let ((fk (function-keys)))
  (report "func/vector"
          (if (vector? fk) 'PASS 'FAIL))
  (define (slot-check idx expected)
    (let ((got (and (vector? fk) (< idx (vector-length fk))
                    (vector-ref fk idx))))
      (if (equal? got expected)
          'PASS
          (list 'FAIL 'idx idx 'expected expected 'got got))))
  (report "func/f1"     (slot-check 190 "f1"))
  (report "func/f35"    (slot-check 224 "f35"))
  (report "func/delete" (slot-check 255 "delete")))

;;; --- Case 3: iso function keys still contains "iso-lefttab".
(let ((iso (iso-fk)))
  (report "iso/vector"
          (if (vector? iso) 'PASS 'FAIL))
  (report "iso/lefttab"
          (if (and (vector? iso) (member "iso-lefttab" (vector->list iso)))
              'PASS
              'FAIL)))

;;; --- Case 4: multimedia keys DEFUN returns a vector.  Empty on
;;; non-NTGUI builds; non-empty where MULTIMEDIA_KEY_EVENT can fire.
(let ((mm (mm-keys)))
  (report "mm/vector"
          (if (vector? mm) 'PASS 'FAIL)))

;;; --- Case 5: wheel_syms cache (MES_CACHE_WHEEL) is still sized 4
;;; after the literal swap.
;;; --mes-cache-get returns a Lisp vector, which crosses to Scheme as
;;; an elisp vector (Guile `vector?` is #f), so measure it with the
;;; elisp `length` primitive like modify-event-symbol.scm does.
(let* ((wc (wheel-cache))
       (wc-len ((symbol-function 'length) wc)))
  (report "wheel/cache-length-4"
          (if (= wc-len 4)
              'PASS
              (list 'FAIL 'length wc-len 'value wc))))
