;;; test-m30-imp5.scm --- M30 imp-5: close-out audit proof.
;;;
;;; brief.org (M30 imp-5) close-out.  imp-1 to imp-4 moved the plain
;;; bool, fixnum, and Lisp_Object cells to the cell table and deleted
;;; their per-cell DEFUNs.  imp-5 classifies the 49 names the earlier
;;; steps did not convert.  One name fits the table: the getctag
;;; get/set pair.  imp-5 roots getctag (getctag = Qnil then staticpro),
;;; deletes the two DEFUNs, adds a CELL_LISP_OBJECT row, and defines
;;; the pair as Scheme wrappers.
;;;
;;; The other 47 names stay C.  Their class is an operation, a struct
;;; field, a per-thread macro, or a C function wrapper; none is a plain
;;; cell, so none enters the table.  Reasons: docs/m30-plan.org §imp-5.
;;;
;;; This corpus checks (brief.org §7):
;;;
;;;   1. the converted ctag pair: write through the accessor, read
;;;      through --cell-ref, and compare;
;;;   2. the canonical key --set-ctag is a table key, and a static scan
;;;      of src/keyboard.c shows no per-cell DEFUN for --get-ctag or
;;;      --set-ctag remains (a resolving key alone does not prove the
;;;      DEFUN is gone -- the registration masks a stale one);
;;;   3. --set-ctag keeps its "return TAG" contract;
;;;   4. each of the 47 stay-C names is NOT a table key: --cell-ref
;;;      signals;
;;;   5. the converted object cell survives a forced GC (it is a root);
;;;   6. the corpus reports its check count.
;;;
;;; Sourced by test-m30-imp5.el via eval-scheme.  Accumulates
;;; (NAME STATUS) pairs into test-results for readback from elisp.

(use-modules (ice-9 rdelim))
(use-modules (srfi srfi-13))

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
  "Force a Lisp_Object garbage collection.  A converted object cell is
a staticpro root, so a stored object must survive this."
  ((subr 'garbage-collect)))

(define (slurp path)
  "Return the whole file at PATH as a string, or #f when it is absent."
  (if (not (file-exists? path))
      #f
      (call-with-input-file path
        (lambda (port)
          (let loop ((chars '()))
            (let ((c (read-char port)))
              (if (eof-object? c)
                  (list->string (reverse chars))
                  (loop (cons c chars)))))))))

;;; --- 1/2/5. the converted getctag pair ------------------------------
;;; --set-ctag is the canonical table key.  --get-ctag is a Scheme
;;; wrapper that reads the same row.

(define ctag-key '--set-ctag)

(let ((old (cell-ref ctag-key)))
  ;; 1. A write through the named Scheme accessor, a read through the
  ;;    table.  The deleted DEFUN was this same plain write.
  ((subr '--set-ctag) (list 'accessor-write 'ctag))
  (check "ctag/accessor-set-table-read"
         (list 'accessor-write 'ctag) (cell-ref ctag-key))
  ;; 2. The canonical key is a table key: --cell-ref resolves it.  (This
  ;;    alone does not prove the DEFUN is gone; the static scan below
  ;;    does, since the registration masks a stale subr.)
  (check "ctag/canonical-key-in-table" #t
         (not (signals? (lambda () (cell-ref ctag-key)))))
  ;; --get-ctag reads the same cell as the table key.
  (check "ctag/getter-reads-table"
         (list 'accessor-write 'ctag) ((subr '--get-ctag)))
  ;; 3. --set-ctag returns TAG (mirrors set-current-kboard; the contract
  ;;    main-queue.scm:131 and test-m12-shims.scm depend on).
  (check "ctag/set-returns-tag" 'the-ctag ((subr '--set-ctag) 'the-ctag))
  (check "ctag/set-effect-visible" 'the-ctag (cell-ref ctag-key))
  ;; 5. GC stress: store a fresh object through the named Scheme
  ;;    accessor, force a garbage collection while only the C cell
  ;;    references it, then read it back through the table and through
  ;;    the getter.  A collected object would give a different value.
  ;;    (getctag is now a staticpro root.)  The write uses --set-ctag,
  ;;    so the wrapper is also covered on the GC path.
  ((subr '--set-ctag) (list 'gc-stress 'ctag))
  (force-gc)
  (check "ctag/gc-stress-table-read"
         (list 'gc-stress 'ctag) (cell-ref ctag-key))
  (check "ctag/gc-stress-getter-read"
         (list 'gc-stress 'ctag) ((subr '--get-ctag)))
  ;; Restore the first value.
  (cell-set! ctag-key old))

;;; --- 2b. the pair's per-cell DEFUNs are gone from the C source -------
;;; The table-key check above shows the key resolves, but the
;;; registration in (emacs cell-accessors) overwrites the function
;;; slot, so a stale DEFUN would be masked.  brief.org §7.2 asks to
;;; confirm no DEFUN remains: scan src/keyboard.c, a static proof.

(if (not (defined? '%m30-root))
    (report "ctag/no-defun:root" (cons 'FAIL "root not bound by wrapper"))
    (let ((body (slurp (string-append %m30-root "/src/keyboard.c"))))
      (if (not body)
          (report "ctag/no-defun:keyboard.c" (cons 'FAIL "file missing"))
          (for-each
           (lambda (name)
             (let ((token (string-append "DEFUN (\"" (symbol->string name) "\"")))
               (if (string-contains body token)
                   (report (string-append "ctag/no-defun:" (symbol->string name))
                           (cons 'FAIL (format #f "DEFUN ~a still present" name)))
                   (report (string-append "ctag/no-defun:" (symbol->string name))
                           'PASS))))
           '(--get-ctag --set-ctag)))))

;;; --- the converted names are registered -----------------------------

(for-each
 (lambda (name)
   (check (string-append "registered:" (symbol->string name)) #t
          (truthy? (subr name))))
 '(--get-ctag --set-ctag))

;;; --- 4. the 47 stay-C names are not table keys ----------------------
;;; brief.org §4 lists 49 remaining names; the getctag pair above is the
;;; only conversion, so 47 stay C.  A stay-C name must NOT enter the
;;; table: --cell-ref signals for it.

(define stay-c-names
  '(;; --set- family (22; --set-ctag is converted)
    --set-buffer-from-selected-window
    --set-button-down-time
    --set-current-kboard-immediate-echo
    --set-force-quit-count!
    --set-ie-arg
    --set-ie-code
    --set-ie-frame-or-window
    --set-ie-modifiers
    --set-kboard-kbd-queue-has-data
    --set-rks-current-binding
    --set-rks-delayed-switch-frame
    --set-rks-disabled-conversion
    --set-rks-echo-start
    --set-rks-fake-prefixed-keys
    --set-rks-key
    --set-rks-keys-start
    --set-rks-mock-input
    --set-rks-starting-buffer
    --set-rks-t
    --set-rks-used-mouse-menu
    --set-this-command-key-count
    --set-this-single-command-key-start
    ;; --clear- family (8)
    --clear-current-kboard-immediate-echo
    --clear-executing-kbd-macro
    --clear-executing-kbd-macro-c-only
    --clear-force-start-and-flush-buffer-unchanged
    --clear-input-available-clear-time!
    --clear-message-1-0
    --clear-recent-keys-ring
    --clear-waiting-for-input
    ;; --get- family (6; --get-ctag is converted)
    --get-input-pending
    --get-keymap
    --get-keysym-name
    --get-large-narrowing-begv
    --get-large-narrowing-zv
    --get-tab-bar-item-kbd
    ;; --selected- family (8)
    --selected-frame-glyphs-initialized-p
    --selected-frame-initial-p
    --selected-frame-kboard
    --selected-frame-live-p
    --selected-frame-tty-flow-control-p
    --selected-frame-tty-meta-key
    --selected-frame-tty-p
    --selected-window-buffer-current-p
    ;; --current- family (3)
    --current-buffer-mark-active-p
    --current-buffer-mark-has-buffer-p
    --current-kboard-immediate-echo-p))

(for-each
 (lambda (name)
   (check (string-append "stay-c-not-in-table:" (symbol->string name)) #t
          (signals? (lambda () (cell-ref name)))))
 stay-c-names)

;;; 6. Report the stay-C count so the audit is a count, not a ladder.

(check "stay-c/count" 47 (length stay-c-names))
