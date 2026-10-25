;;; SRFI-64 tests for the standalone loader and Elisp reader/evaluator.

(use-modules (srfi srfi-64)
             (emacs loader)
             (emacs-elisp runtime))

;; Pinned case count.  A suite that loses a case must fail (cr.org of the
;; M59 imp-5 round, F3: the round file is reused, so name the round).
;; M60 imp-14: 6 -> 8, the 2 `defalias' cases of row 34.
;; M60 imp-15: 8 -> 12, the 4 hash cases of row 32; 12 -> 13 for the
;; ACCESSOR case of brief.org P1.
;; M60 imp-16: 13 -> 15, the 2 cases of row 25
;; (`normal-top-level-add-to-load-path'): 1 negative and 1 positive.
;; cr.org F1 fix: 15 -> 17, the TAIL-cell anchor case and the ABSENT
;; anchor case (the elisp loop splices at the tail cell too).
;; M60 imp-17: 17 -> 19, the 2 cases of F3 (the guarded `featurep'
;; install): 1 for the cell and 1 for its 2 answers.
(define expected-passes 19)

;; No SRFI-64 log file: it would land in the working directory (cr.org F4).
(set! test-log-to-file #f)

(define repo-root (getenv "GUILEMACS_ROOT"))
(unless repo-root
  (error "GUILEMACS_ROOT must be set by run-mod-tests.sh"))

(define (fixture file)
  (string-append repo-root "/test/mod/" file))
(define runtime-module (resolve-module '(emacs-elisp runtime)))

(define (load-fixture file)
  "Load FILE with the standalone runtime as the current module."
  (save-module-excursion
   (lambda ()
     (set-current-module runtime-module)
     (elisp-load (fixture file)))))

(test-begin "Guilemacs standalone loader and reader")
(define test-runner (test-runner-current))

;; Initialize in plain Guile.  This suite does not start Emacs or loadup.el.
;; The handler keeps the condition key and arguments, so a failure names its
;; cause instead of a bare #f (cr.org N2).
(define init-result
  (catch #t
    (lambda ()
      (save-module-excursion
       (lambda () (init-loader (string-append repo-root "/prelude"))))
      #t)
    (lambda (key . args) (cons 'error (cons key args)))))
(test-assert (format #f "init-loader starts in plain Guile (result: ~s)"
                     init-result)
             (eq? #t init-result))

;;; M60 imp-17 -- F3: the `featurep' cell of (emacs utils) :493, installed
;;; by the guarded block of `init-loader'.  The C owner is `Ffeaturep'
;;; (src/fns.c :3432); the guard keeps that cell in a full Emacs.  The
;;; suite imports (emacs loader) and (emacs-elisp runtime) only, so the
;;; cases call the INSTALLED cells, not the `elisp-*' names.

;; Case 1 -- the CELL is present after `init-loader'.
(test-assert "row F3: `init-loader' installs the `featurep' cell"
             (eq? #t (symbol-fbound? 'featurep)))

;; Case 2 -- the CELL answers.  `provide' adds the feature to the
;; `features' list that the cell reads, so this case does not rely on that
;; bind alone (F4 keeps the bind `()').  An absent feature must give
;; `#nil', and `(eq? #nil #f)' is FALSE, so the 2 words are pinned apart.
;; cr.org F4 of this round: `provide' MUTATES the global `features' list,
;; so the case SAVES the list and RESTORES it.  No later case sees
;; `m60-imp17', and the restore is part of the assertion.
(let* ((features-before (and (symbol-bound? 'features)
                             (symbol-value 'features)))
       (provide-cell (and (symbol-fbound? 'provide)
                          (symbol-function 'provide)))
       (featurep-cell (and (symbol-fbound? 'featurep)
                           (symbol-function 'featurep)))
       (added (and provide-cell
                   (apply provide-cell '(m60-imp17))))
       (present (and featurep-cell
                     (apply featurep-cell '(m60-imp17))))
       (absent (and featurep-cell
                    (apply featurep-cell '(m60-imp17-absent))))
       (answers? (and added
                      (eq? #t present)
                      (eq? #nil absent))))
  (when (symbol-bound? 'features)
    (set-symbol-value! 'features features-before))
  (test-assert (format #f "row F3: the installed `featurep' cell answers #t for a provided feature and #nil for an absent one (present: ~s, absent: ~s, features restored: ~s)"
                       present absent
                       (and (symbol-bound? 'features)
                            (equal? features-before (symbol-value 'features))))
               (and answers?
                    (symbol-bound? 'features)
                    (equal? features-before (symbol-value 'features)))))

;; This fixture defines and calls an Elisp function, then stores its result.
(let ((result
       (catch #t
         (lambda () (load-fixture "standalone-loader.el") 'loaded)
         (lambda (key . args) (list 'error key args)))))
  (test-eq (format #f "loader reads and evaluates standalone Elisp (result: ~s)"
                   result)
           'loaded result))
(test-equal "evaluated Elisp side effect is observable"
            42
            (and (symbol-bound? 'standalone-loader-test-result)
                 (symbol-value 'standalone-loader-test-result)))

;; A reader-only path would not signal this error.  Evaluation must raise
;; void-function for the deliberately unbound call.
(let ((result
       (catch #t
         (lambda () (load-fixture "standalone-loader-error.el") 'loaded)
         (lambda (key . args) key))))
  (test-eq (format #f "loader propagates void-function from evaluation (key: ~s)"
                   result)
           'void-function result))

;; The elisp `set' cell of row 33 (M60 imp-13): `set' stores the VALUE
;; cell and returns NEWVAL, and a non-symbol raises.  The C owner is
;; src/data.c :1317.  The reader applies this cell for every `:keyword'
;; form (reader.scm :1358).
(let* ((set-fn (and (symbol-fbound? 'set) (symbol-function 'set)))
       (ret (and set-fn (apply set-fn '(standalone-set-test-var 42))))
       (stored (and (symbol-bound? 'standalone-set-test-var)
                    (symbol-value 'standalone-set-test-var)))
       (err (catch #t
              (lambda () (apply set-fn '("standalone-set-test-str" 1)) 'no-error)
              (lambda (key . args) (cons key args)))))
  ;; Guile stores a `misc-error' payload FLAT: a format string and its
  ;; argument list are 2 ADJACENT elements.  `init-loader' gives `error'
  ;; the elisp binding, so the measured shape is
  ;;   (misc-error #f "~A ~S" (MSG OBJ) #f).
  ;; The FORMATTED text is the stable token, so both shapes match it.
  (define (payload-text items)
    (cond ((or (null? items) (null? (cdr items))) #f)
          ((and (string? (car items)) (list? (cadr items)))
           (apply format #f (car items) (cadr items)))
          (else (payload-text (cdr items)))))
  (test-assert "elisp `set' stores the value cell and returns NEWVAL"
               (and (eq? #t (symbol-fbound? 'set))
                    (equal? 42 ret)
                    (equal? 42 stored)
                    (pair? err)
                    (eq? 'misc-error (car err))
                    (equal? (format #f "Wrong type argument: symbolp ~S"
                                    "standalone-set-test-str")
                            (payload-text (cdr err))))))

;; Row 33 on the real reader path: this fixture holds a :keyword form,
;; so `elisp-intern-and-make-keyword' (reader.scm :1358) applies the
;; `set' cell while it reads.  An empty cell raised wrong-type-arg.
;; The module `equal?' is not the Guile one (it does not compare lists),
;; so the 3 elements and the terminating nil are pinned one by one.
(let ((result (catch #t
                (lambda () (load-fixture "standalone-keyword.el") 'loaded)
                (lambda (key . args) (list 'error key args)))))
  (test-assert (format #f "reader handles a :keyword form (result: ~s)" result)
               (and (eq? 'loaded result)
                    (symbol-bound? 'standalone-keyword-test-result)
                    (let ((v (symbol-value 'standalone-keyword-test-result)))
                      (and (eq? (car v) (string->symbol ":keyword-a"))
                           (equal? (cadr v) 1)
                           (eq? (caddr v) (string->symbol ":keyword-b"))
                           (null? (cdddr v)))))))

;;; M60 imp-14 -- row 34: the `defalias' cell (utils.scm :235), the
;;; UNEVALLED `function' form (loader.scm :1209) and the symbol-cell
;;; indirection of `elisp-loader-apply' (loader.scm :1106).  C owner is
;;; `Fdefalias' (src/data.c :706).  The suite runs in plain Guile, so the
;;; 2 cases below are the automatic gate of the row.

;; The MESSAGE of the Guile `misc-error' of an elisp `(error FMT . ARGS)'
;; call, or #f.  Guile stores the payload FLAT: the format string and its
;; argument list are 2 ADJACENT elements.  The case above has its own
;; copy of this walk inside its `let'; this one is shared by the 2 cases
;; of row 34.
(define (row34-error-text items)
  (cond ((or (null? items) (null? (cdr items))) #f)
        ((and (string? (car items)) (list? (cadr items)))
         (apply format #f (car items) (cadr items)))
        (else (row34-error-text (cdr items)))))

;; Case 1 -- the CELL and the CALL.  `standalone-alias.el' is the real
;; reader and evaluator path: `defun', `#'x' (which reads to
;; `(function x)'), `defalias', then a CALL of the alias.  The cell must
;; hold the SOURCE SYMBOL, not a procedure: C stores the definition as
;; written and resolves it at CALL time (`indirect_function').  The
;; `defalias' return value is the SYMBOL, not the definition (bug#11686).
(let* ((alias-fn (and (symbol-fbound? 'defalias) (symbol-function 'defalias)))
       (result (catch #t
                 (lambda () (load-fixture "standalone-alias.el") 'loaded)
                 (lambda (key . args) (list 'error key args))))
       (ret (and alias-fn
                 (apply alias-fn '(standalone-alias-return-probe
                                   standalone-alias-source))))
       (cell (and (symbol-fbound? 'standalone-alias-target)
                  (symbol-function 'standalone-alias-target))))
  (test-assert (format #f "elisp `defalias' writes the SYMBOL cell, returns SYMBOL and the CALL follows the cell (result: ~s, cell: ~s)"
                       result cell)
               (and (eq? 'loaded result)
                    (eq? 'standalone-alias-source cell)
                    (eq? 'standalone-alias-return-probe ret)
                    (symbol-bound? 'standalone-alias-test-result)
                    (equal? 42 (symbol-value 'standalone-alias-test-result)))))

;; Case 2 -- the RAISE.  A ring A -> B -> A must raise
;; `cyclic-function-indirection' and must NOT hang; the raise names the
;; symbol of the CALL, not the symbol that closes the ring.  A non-symbol
;; ARG 1 must raise the `symbolp' shape of `elisp-put'.  The 100-link
;; count of the resolver is a guilemacs SAFETY: C has no count here.
(let* ((alias-fn (and (symbol-fbound? 'defalias) (symbol-function 'defalias)))
       (eval-form (module-ref (resolve-module '(emacs loader))
                              'elisp-loader-eval))
       (ring (and alias-fn
                  (begin
                    (apply alias-fn '(standalone-alias-ring-a
                                      standalone-alias-ring-b))
                    (apply alias-fn '(standalone-alias-ring-b
                                      standalone-alias-ring-a)))))
       (cycle (and ring
                   (catch #t
                     (lambda () (eval-form '(standalone-alias-ring-a)) 'no-error)
                     (lambda (key . args) (cons key args)))))
       (type-err (and alias-fn
                      (catch #t
                        (lambda ()
                          (apply alias-fn '("standalone-alias-str"
                                            standalone-alias-source))
                          'no-error)
                        (lambda (key . args) (cons key args)))))
       (text (and (pair? type-err) (row34-error-text (cdr type-err)))))
  (test-assert (format #f "elisp `defalias' raises `cyclic-function-indirection' on a symbol ring and `symbolp' on a non-symbol (cycle: ~s, type: ~s)"
                       cycle (and (pair? type-err) (car type-err)))
               (and (eq? 'cyclic-function-indirection (and (pair? cycle) (car cycle)))
                    (equal? '(standalone-alias-ring-a) (cdr cycle))
                    (eq? 'misc-error (and (pair? type-err) (car type-err)))
                    ;; The FORMATTED text is the stable token: the
                    ;; payload shape differs between Guile versions.
                    (equal? "Wrong type argument: symbolp \"standalone-alias-str\""
                            text))))

;;; M60 imp-15 -- row 32: the `make-hash-table' family.  The C owner is
;;; `Fmake_hash_table' (src/fns.c :5253).  1 SRFI-69 table IS the elisp
;;; object (D1), so the 5 `Hash case' blocks below run the INSTALLED cells
;;; that `init-loader' put in place, and `standalone-hash.el' is the real
;;; reader and evaluator path of the same cells.  These blocks and the 7
;;; fixture blocks use 1 numbering: each case names the fixture blocks
;;; that it reads.

;; `every' is NOT bound in this module (measured: the call raised), and
;; the suite imports no list library, so this loop is local.
(define (all-fbound? names)
  (or (null? names)
      (and (eq? #t (symbol-fbound? (car names)))
           (all-fbound? (cdr names)))))

;; Hash case 1 -- the CELLS, the call and the `equal'/`eq' test mapping
;; (D2).  It reads fixture `Hash case 1' and `Hash case 2'.
;; `standalone-hash.el' stores every result, so a reader or evaluator
;; defect fails here too.  The 14 names are the 13 exports of
;; (emacs utils) plus `hash-table-p'.
(let ((cells '(make-hash-table gethash puthash remhash clrhash
                hash-table-p hash-table-count))
      (result (catch #t
                (lambda () (load-fixture "standalone-hash.el") 'loaded)
                (lambda (key . args) (list 'error key args))))
      (value (lambda (sym)
               (and (symbol-bound? sym) (symbol-value sym)))))
  (test-assert (format #f "row 32 hash cells are installed and the fixture loads (result: ~s)"
                       result)
               (and (eq? 'loaded result)
                    (all-fbound? cells)
                    ;; `puthash' returns the VALUE, twice.
                    (equal? 42 (value 'standalone-hash-put-ret))
                    (equal? 43 (value 'standalone-hash-put-ret-2))
                    (equal? 42 (value 'standalone-hash-found))
                    ;; An absent key gives the elisp nil, and the DEFAULT
                    ;; when the caller gives one.
                    (eq? #nil (value 'standalone-hash-absent))
                    (eq? 'standalone-hash-fallback
                         (value 'standalone-hash-default))
                    ;; The `equal' table finds an `equal?' but not `eq?'
                    ;; copy; the `eq' table does not.
                    (eq? 'standalone-hash-list-value
                         (value 'standalone-hash-equal-hit))
                    (eq? 'standalone-hash-absent
                         (value 'standalone-hash-eq-miss))
                    (equal? 2 (value 'standalone-hash-eq-count))
                    (equal? 2 (value 'standalone-hash-count))
                    ;; `hash-table-p': t for a table, nil for a list.
                    (eq? #t (value 'standalone-hash-p))
                    (eq? #nil (value 'standalone-hash-list-p)))))

;; Hash case 2 -- the DEFAULT test is `eql' (C :5314), and a REPEATED
;; keyword keeps the FIRST value, because the C loop :5294 reads the
;; argument vector RIGHT to LEFT.  `eq' first means the 2 `equal?' keys stay 2.
;; It reads fixture `Hash case 3', `Hash case 4' and `Hash case 5'.
(let ((value (lambda (sym)
               (and (symbol-bound? sym) (symbol-value sym)))))
  (test-assert "row 32 hash: the default test is eql and a repeated keyword keeps the first value"
               (and (equal? 2 (value 'standalone-hash-default-count))
                    (equal? 2 (value 'standalone-hash-nil-test-count))
                    (equal? 2 (value 'standalone-hash-repeat-count))
                    ;; A valid `:weakness', `:purecopy' and the 2
                    ;; obsolete rehash keywords are ACCEPTED, and the
                    ;; result is still a table.
                    (eq? #t (value 'standalone-hash-keywords-p)))))

;; Hash case 3 -- the 7 ACCESSOR cells of brief.org P1, called through the
;; elisp path (fixture `Hash case 7').  Before this repair the ONLY reach
;; was `module-ref', which is a module-load proof, not an elisp call.
(let ((value (lambda (sym)
               (and (symbol-bound? sym) (symbol-value sym)))))
  (test-assert "row 32 hash: the 7 accessor cells answer through the elisp path"
               (and (eq? 'equal (value 'standalone-hash-accessor-test))
                    ;; L38: the ENTRY count, not the allocation size.
                    (equal? 1 (value 'standalone-hash-accessor-size))
                    ;; L37: every table is STRONG.
                    (eq? #nil (value 'standalone-hash-accessor-weakness))
                    (equal? 1.5 (value 'standalone-hash-accessor-rehash-size))
                    (equal? 0.8125
                            (value 'standalone-hash-accessor-rehash-threshold))
                    (pair? (value 'standalone-hash-accessor-keys))
                    (eq? 'standalone-hash-ak
                         (car (value 'standalone-hash-accessor-keys)))
                    (pair? (value 'standalone-hash-accessor-values))
                    (eq? 7
                         (car (value 'standalone-hash-accessor-values))))))

;; Hash case 4 -- `remhash' returns the elisp nil in BOTH cases (C :5491
;; returns Qnil with no test for presence), and `clrhash' returns the
;; SAME table with 0 entries.
(let ((value (lambda (sym)
               (and (symbol-bound? sym) (symbol-value sym)))))
  (test-assert "row 32 hash: remhash returns nil in both cases and clrhash returns the same table"
               (and (eq? #nil (value 'standalone-hash-remhash-ret))
                    (eq? #nil (value 'standalone-hash-remhash-absent))
                    (equal? 1 (value 'standalone-hash-count-after-remhash))
                    (eq? #t (value 'standalone-hash-clear-same))
                    (equal? 0 (value 'standalone-hash-count-after-clear)))))

;; Hash case 5 -- the 5 RAISE shapes that the C constructor and the C
;; accessors own: odd count (:5293), unknown keyword (:5309), invalid
;; size (:5330), invalid weakness (:5344) and a non-table argument.
;; A raise aborts an elisp LOAD, so the calls are Scheme-level calls of
;; the SAME cells that the reader installed.
(let* ((make-fn (and (symbol-fbound? 'make-hash-table)
                     (symbol-function 'make-hash-table)))
       (gethash-fn (and (symbol-fbound? 'gethash)
                        (symbol-function 'gethash)))
       (kw (lambda (name) (string->symbol name)))
       (text (lambda (thunk)
               (let ((err (catch #t
                            (lambda () (thunk) 'no-error)
                            (lambda (key . args) (cons key args)))))
                 (and (pair? err) (row34-error-text (cdr err)))))))
  (test-assert "row 32 hash: the 5 raise shapes match the C texts"
               (and (equal? "Odd number of arguments"
                            (and make-fn
                                 (text (lambda () (make-fn (kw ":test"))))))
                    (equal? "Invalid keyword argument :bogus"
                            (and make-fn
                                 (text (lambda () (make-fn (kw ":bogus") 1)))))
                    (equal? "Invalid hash table size \"x\""
                            (and make-fn
                                 (text (lambda () (make-fn (kw ":size") "x")))))
                    (equal? "Invalid hash table weakness weird"
                            (and make-fn
                                 (text (lambda ()
                                         (make-fn (kw ":weakness") 'weird)))))
                    (equal? "Wrong type argument: hash-table-p (1 2)"
                            (and gethash-fn
                                 (text (lambda () (gethash-fn 'k '(1 2)))))))))

;; M60 imp-16 -- row 25: `normal-top-level-add-to-load-path'.  The port
;; READS `default-directory' (the caller owns the bind, lisp/startup.el
;; :631); it does not bind it.  The NEGATIVE case runs FIRST, because the
;; positive case binds the variable for the rest of the process (the
;; elisp value slot has no "unbind", loader.scm :1140).
(let ((before (length (symbol-value 'load-path))))
  (let ((result (catch #t
                  (lambda () (load-fixture "standalone-ntl.el") 'loaded)
                  (lambda (key . args) (list 'error key args)))))
    (test-assert "row 25: no caller bind of default-directory raises void-variable and leaves load-path alone"
                 (and (equal? '(error void-variable (default-directory)) result)
                      (= before (length (symbol-value 'load-path)))))))

;; The positive case: the 2 expanded names follow the ANCHOR entry, which
;; is the stripped `default-directory'.  A `done' load is not expansion
;; proof; the 2 joined values at the anchor cell are.  This bind is the
;; caller bind of lisp/startup.el :631.
(set-symbol-value! 'default-directory (string-append repo-root "/lisp/"))
(let* ((before (length (symbol-value 'load-path)))
       (dd (symbol-value 'default-directory))
       (anchor (substring dd 0 (- (string-length dd) 1)))
       (result (catch #t
                 (lambda () (load-fixture "standalone-ntl.el") 'loaded)
                 (lambda (key . args) (list 'error key args))))
       (lp (symbol-value 'load-path))
       (at (let loop ((l lp) (i 0))
             (cond ((null? l) #f)
                   ((equal? anchor (car l)) i)
                   (else (loop (cdr l) (+ i 1)))))))
  (test-assert "row 25: the 2 names are expanded and spliced after the anchor entry"
               (and (eq? 'loaded result)
                    (= (+ before 2) (length lp))
                    at
                    (equal? (string-append anchor "/m60ntla")
                            (list-ref lp (+ at 1)))
                    (equal? (string-append anchor "/m60ntlb")
                            (list-ref lp (+ at 2))))))

;; F1 of the cr.org review of imp-16: the elisp loop stops on the TAIL
;; cell of `load-path' and STILL splices after it (`(when tail
;; (setcdr tail ...))', lisp/startup.el :495).  The plain path keeps the
;; anchor at index 0 of 14, so the 2 cases above never reach the tail
;; cell.  These 2 do: 1 with the anchor AT the tail cell, 1 with no
;; anchor at all (elisp splices after the LAST cell).  Both put the OLD
;; `load-path' back: the value slot is process-global.
(let* ((saved (symbol-value 'load-path))
       (dd (symbol-value 'default-directory))
       (anchor (substring dd 0 (- (string-length dd) 1)))
       (ntl-run (lambda (lp)
                  (set-symbol-value! 'load-path lp)
                  (catch #t
                    (lambda () (load-fixture "standalone-ntl.el") 'loaded)
                    (lambda (key . args) (list 'error key args))))))
  (let ((result (ntl-run (list "/tmp/m60ntl-a" anchor))))
    (test-assert "row 25: the anchor AT the TAIL cell of load-path still takes the 2 names"
                 (and (eq? 'loaded result)
                      (equal? (list "/tmp/m60ntl-a" anchor
                                    (string-append anchor "/m60ntla")
                                    (string-append anchor "/m60ntlb"))
                              (symbol-value 'load-path)))))
  (let ((result (ntl-run (list "/tmp/m60ntl-a" "/tmp/m60ntl-b"))))
    (test-assert "row 25: an ABSENT anchor appends the 2 names after the last cell"
                 (and (eq? 'loaded result)
                      (equal? (list "/tmp/m60ntl-a" "/tmp/m60ntl-b"
                                    (string-append anchor "/m60ntla")
                                    (string-append anchor "/m60ntlb"))
                              (symbol-value 'load-path)))))
  (set-symbol-value! 'load-path saved))

(test-end "Guilemacs standalone loader and reader")

(let ((passes (test-runner-pass-count test-runner))
      (fails  (test-runner-fail-count test-runner)))
  (format #t "~a: ~a passed, ~a failed (expected ~a passed)~%"
          "Guilemacs standalone loader and reader" passes fails
          expected-passes)
  (exit (if (and (zero? fails) (= passes expected-passes)) 0 1)))
