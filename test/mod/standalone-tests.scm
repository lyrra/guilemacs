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
;; M60 imp-18 (19 -> 22): the 3 cases of row 35 (the guarded
;; `bare-symbol' install): 1 for the cell, 1 for the identity, and 1 for
;; the elisp nil (the 3rd truth value).
;; M60 imp-19 (22 -> 32): the 10 cases of limit L4 (`&optional' and
;; `&rest' in a parameter list): 5 fixture cases and 5 malformed-shape
;; cases.  cr.org FIX of the imp-19 round (32 -> 36, OLD value 32): cases
;; 11 ... 14 gate the 2 limits that had no case, L45 (lenient arity) and
;; L46 (a non-list parameter list), plus D1 for several `&optional' names.
;; M60 imp-20 (36 -> 42): the 6 cases of row 36 (the `declare' form is
;; data): the fixture loads, the value is the elisp nil, the argument is
;; not evaluated, a DOTTED shape is legal too, a declaration as the first
;; body form of a macro is ignored, and the load continues.  The dotted
;; case answers cr.org of the imp-20 round, F8: L51 stated that property
;; and no case loaded it.
;; cr.org F7 fix of the imp-20 round (42 -> 43, OLD value 42): case 7
;; gates limit L14 at CALL time: a declaration in the body of a `defun'
;; is data, so the call answers the body value and does not raise.
;; M60 imp-21 (43 -> 48): the 5 cases of row 28b (the `backquote' value
;; builder): the fixture loads, `,' evaluates and `,@' splices at depth 1,
;; a nested backquote keeps both heads at depth 2, the load continues, and
;; `,@' of a non-list raises (L54, L55).
;; cr.org FIX of the imp-21 round (48 -> 51): 3 cases for the 2 behavior
;; findings and 1 missing gate: a nested `,@' at depth 2 keeps its
;; structure and does not raise (F2), a VECTOR argument is walked and a
;; depth-1 `,@' spreads inside it (F3), and the L56 raise of a `,@' in a
;; value context has a case (F8).
;; M60 imp-21 cr.org FIX 2 (51 -> 53): 2 cases for the 2 findings that had
;; no gate: the SHAPE of a delayed unquote with a COMPOUND argument (F6:
;; the shape claim is refuted by lisp/emacs-lisp/backquote.el :121, and
;; the case would catch a dotted pair), and L58, an unquote with 2
;; arguments (F8).  The reader can NOT write the L58 shape: `,` takes 1
;; form, so `(, a b)' reads as `((, a) b)'; the case BUILDS the form.
;; M60 imp-22 (53 -> 61): the 8 cases of row 37 (the guarded `purecopy'
;; identity install): the cell, the identity for a symbol, an integer,
;; the elisp nil and a string, the MUTABLE-object limit L59 (a cons
;; comes back as the SAME cons), and the fixture load, whose macro
;; expander body calls the cell at load time.
;; M60 imp-22 cr.org FIX (60 -> 61, OLD value 60): 1 case for the type
;; that cr.org section 5 left NOT measured: an AGGREGATE object (a vector
;; and a hash table) comes back as the SAME object too.
;; M60 imp-22 cr.org F5 FIX: the pre-fix text of this block counted "7
;; cases"; MEASURED are 8 `test-assert' forms (`Case 1' ... `Case 8'), so
;; the text and the pin 61 agree now.
;; M60 imp-22 cr.org review of 18e00220f, F3 and F6: case 1 now asserts
;; `procedure?' (a stub VALUE in the cell fails it) and case 3 drops the
;; CONSTANT form `(not (eq? #nil #f))'.  Comments and 1 assertion only,
;; so the pin stays 61.
(define expected-passes 61)

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

;;; M60 imp-18 -- row 35: the `bare-symbol' cell of (emacs types) :426,
;;; installed by the guarded block of `init-loader'.  The C owner is
;;; `Fbare_symbol' (src/data.c :599) and its argument vector 1, 1, 0
;;; names NO type predicate, so the function is the IDENTITY.

;; Case 1 -- the CELL is present after `init-loader'.
(test-assert "row 35: `init-loader' installs the `bare-symbol' cell"
             (eq? #t (symbol-fbound? 'bare-symbol)))

;; Case 2 -- the CELL is the IDENTITY.  It answers the SAME symbol
;; (`eq?', not `equal?'), and a NUMBER comes back unchanged with NO
;; raise: the C function has no type predicate, so `wrong-type-argument'
;; here would be a defect.
(let* ((cell (and (symbol-fbound? 'bare-symbol)
                  (symbol-function 'bare-symbol)))
       (sym (and cell (apply cell '(m60-imp18))))
       (num (and cell
                 (catch #t
                   (lambda () (list 'ok (apply cell '(42))))
                   (lambda (key . args) (cons 'error (cons key args)))))))
  (test-assert (format #f "row 35: the installed `bare-symbol' cell returns the SAME symbol and a number unchanged, with no raise (sym: ~s, num: ~s)"
                       sym num)
               (and (eq? sym 'm60-imp18)
                    (equal? num '(ok 42)))))

;; Case 3 -- the elisp nil passes through unchanged with NO raise.  The
;; C DEFUN has no type predicate, so a raise here would be a defect, and
;; `#nil' must stay `#nil' (`equal?', the 3 truth values are kept).
(let ((result (and (symbol-fbound? 'bare-symbol)
                   (catch #t
                     (lambda ()
                       (list 'ok (apply (symbol-function 'bare-symbol)
                                        (list #nil))))
                     (lambda (key . args) (cons 'error (cons key args)))))))
  (test-assert (format #f "row 35: the elisp nil passes through the installed `bare-symbol' cell unchanged, with no raise (result: ~s)"
                       result)
               (equal? result (list 'ok #nil))))

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

;;; M60 imp-19 -- L4: `&optional' and `&rest' in a parameter list.  The
;;; binder `elisp-loader-bind-params!' is NOT exported, so these cases run
;;; the REAL reader and evaluator: `standalone-optional.el' holds the 3
;;; shapes of brief.org section 8, and the malformed shapes reach the walk
;;; through `elisp-loader-eval' of a `defun' whose BODY is the marker
;;; symbol, so the body returns the VALUE CELL of that name.  C peer:
;;; `funcall_lambda' (src/eval.c :2167).

(define m19-null (and (symbol-fbound? 'null) (symbol-function 'null)))
(define m19-eval (module-ref (resolve-module '(emacs loader))
                             'elisp-loader-eval))

;; (ok VALUE) or (error KEY . ARGS): a raise must be READ, not fatal.
(define (m19-try thunk)
  (catch #t
    (lambda () (list 'ok (thunk)))
    (lambda (key . args) (cons 'error (cons key args)))))

(define (m19-cell name)
  (and (symbol-bound? name) (symbol-value name)))

;; The `&rest' value is a plain Scheme list (L47), so its tail is the
;; Scheme (), not the elisp nil.
(define (m19-scheme-list? value elems)
  (let loop ((v value) (l elems))
    (cond ((null? l) (null? v))
          ((pair? v) (and (eqv? (car v) (car l)) (loop (cdr v) (cdr l))))
          (else #f))))

;; The elisp `list' cell ends its result with the elisp nil `#nil', not
;; with the Scheme (), so the ELEMENTS are compared 1 by 1 and the TAIL is
;; read through the elisp `null' cell.
(define (m19-elems? value elems)
  (let loop ((v value) (l elems))
    (cond ((null? l) (and m19-null (eq? #t (m19-null v))))
          ((pair? v) (and (eqv? (car v) (car l)) (loop (cdr v) (cdr l))))
          (else #f))))

;; Cases 1 ... 5 read the fixture.  Both markers must stay UNBOUND after
;; the load: a marker writes NO cell (D2).
(let* ((load-result (m19-try (lambda ()
                               (load-fixture "standalone-optional.el")
                               'loaded)))
       (loaded (eq? 'loaded (cadr load-result)))
       (m2 (m19-cell 'standalone-optional-m-2))
       (m1 (m19-cell 'standalone-optional-m-1))
       (f2 (m19-cell 'standalone-optional-f-2))
       (f1 (m19-cell 'standalone-optional-f-1))
       (f0 (m19-cell 'standalone-optional-f-0))
       (g4 (m19-cell 'standalone-optional-g-4)))
  ;; Case 1 -- both arguments present: `b' is the 2nd argument.
  (test-assert (format #f "L4 case 1: `(a &optional b)' with 2 arguments binds b to the 2nd argument (load: ~s, value: ~s)"
                       load-result m2)
               (and loaded
                    (pair? m2)
                    (eqv? 1 (car m2))
                    (eqv? 2 (cadr m2))
                    (eq? #t (m19-null (cddr m2)))))
  ;; Case 2 -- 1 argument: `b' is the elisp nil `#nil', and NOT `#f' (D1).
  (test-assert (format #f "L4 case 2: a missing optional argument binds the elisp nil #nil and not #f (value: ~s)"
                       m1)
               (and loaded
                    (pair? m1)
                    (eqv? 1 (car m1))
                    (eq? #nil (cadr m1))
                    (not (eq? #f (cadr m1)))))
  ;; Case 3 -- `&rest' for 2, 1 and 0 extra arguments: 3 different lists
  ;; (D3).  The 0 case is the Scheme (), so the elisp `null' cell answers
  ;; #t for it while `(eq? #nil REST)' is #f.
  (test-assert (format #f "L4 case 3: `&rest' binds the whole remaining list for 2, 1 and 0 extra arguments (2: ~s, 1: ~s, 0: ~s)"
                       f2 f1 f0)
               (and loaded
                    (pair? f2) (eqv? 1 (car f2))
                    (m19-scheme-list? (cadr f2) '(2 3))
                    (pair? f1) (eqv? 1 (car f1))
                    (m19-scheme-list? (cadr f1) '(2))
                    (pair? f0) (eqv? 1 (car f0))
                    (null? (cadr f0))
                    (eq? #t (m19-null (cadr f0)))
                    (not (eq? #nil (cadr f0)))))
  ;; Case 4 -- the 3 shapes in 1 call: `(a &optional b &rest c)'.
  (test-assert (format #f "L4 case 4: `(a &optional b &rest c)' binds all 3 shapes in 1 call (value: ~s)"
                       g4)
               (and loaded
                    (pair? g4)
                    (eqv? 1 (car g4))
                    (eqv? 2 (cadr g4))
                    (m19-scheme-list? (caddr g4) '(3 4))))
  ;; Case 5 -- no cell for a marker (D2).
  (test-assert (format #f "L4 case 5: `&optional' and `&rest' are UNBOUND after the load, so a marker writes no cell (optional: ~s, rest: ~s)"
                       (symbol-bound? '&optional) (symbol-bound? '&rest))
               (and loaded
                    (not (symbol-bound? '&optional))
                    (not (symbol-bound? '&rest)))))

;; Case 6 runs FIRST of cases 6 ... 10: only this case must see `&rest'
;; UNBOUND.  The restore thunk of a name that was unbound leaves elisp nil
;; in the cell, so a later bare `&rest' call would not raise.
(let* ((def (m19-try (lambda ()
                       (m19-eval '(defun m19-optional-bare-rest
                                    (a &rest) &rest)))))
       (call (m19-try (lambda ()
                        (m19-eval '(m19-optional-bare-rest 1))))))
  (test-assert (format #f "L4 case 6: a bare `&rest' stops the walk and writes no cell, so the body raises void-variable (call: ~s, unbound: ~s)"
                       call (not (symbol-bound? '&rest)))
               (and (eq? 'ok (car def))
                    (eq? 'error (car call))
                    (eq? 'void-variable (cadr call))
                    (eq? '&rest (caddr call))
                    (not (symbol-bound? '&rest)))))

;; Case 7 -- `(a &rest &rest)': the 2nd marker IS the rest name, so its
;; cell holds the remaining list (L46).
(let* ((def (m19-try (lambda ()
                       (m19-eval '(defun m19-optional-double-rest
                                    (a &rest &rest) &rest)))))
       (call (m19-try (lambda ()
                        (m19-eval '(m19-optional-double-rest 1 2 3)))))
       (cell (and (eq? 'ok (car call)) (cadr call))))
  (test-assert (format #f "L4 case 7: `(a &rest &rest)' puts the remaining list in the cell of `&rest' (call: ~s)"
                       call)
               (and (eq? 'ok (car def))
                    (eq? 'ok (car call))
                    (m19-scheme-list? cell '(2 3)))))

;; Case 8 -- `(a &rest &optional b)': the walk stops at the rest name, so
;; the marker `&optional' itself becomes the rest name (L46).
(let* ((def (m19-try (lambda ()
                       (m19-eval '(defun m19-optional-rest-then-optional
                                    (a &rest &optional b) &optional)))))
       (call (m19-try (lambda ()
                        (m19-eval '(m19-optional-rest-then-optional 1 2 3)))))
       (cell (and (eq? 'ok (car call)) (cadr call))))
  (test-assert (format #f "L4 case 8: `(a &rest &optional b)' gives the marker `&optional' the remaining list (call: ~s)"
                       call)
               (and (eq? 'ok (car def))
                    (eq? 'ok (car call))
                    (m19-scheme-list? cell '(2 3)))))

;; Case 9 -- a NON-SYMBOL name does not raise at the `defun', and the CALL
;; raises a Guile `wrong-type-arg' (L46).  C raises `invalid-function'.
(let* ((def (m19-try (lambda ()
                       (m19-eval '(defun m19-optional-bad-name (1) 42)))))
       (call (m19-try (lambda () (m19-eval '(m19-optional-bad-name 1))))))
  (test-assert (format #f "L4 case 9: a non-symbol parameter name raises wrong-type-arg at the CALL (def: ~s, call: ~s)"
                       def call)
               (and (eq? 'ok (car def))
                    (eq? 'error (car call))
                    (eq? 'wrong-type-arg (cadr call)))))

;; Case 10 -- `(a &key b)': `&key' is NOT a branch (L48), so it takes the
;; positional step and its cell holds the 2nd argument.
(let* ((def (m19-try (lambda ()
                       (m19-eval '(defun m19-optional-key (a &key b) &key)))))
       (call (m19-try (lambda () (m19-eval '(m19-optional-key 1 2 3)))))
       (cell (and (eq? 'ok (car call)) (cadr call))))
  (test-assert (format #f "L4 case 10: `&key' is out of scope and takes the positional argument (call: ~s)"
                       call)
               (and (eq? 'ok (car def))
                    (eq? 'ok (car call))
                    (eqv? 2 cell))))

;;; M60 imp-19 CR FIX (cr.org section 5, G2 / F5 of the imp-19 round): 4
;;; more cases gate the 2 limit texts that no case measured before.  Cases
;;; 11 and 12 gate L45 (lenient arity: a missing REQUIRED argument and an
;;; EXTRA argument do not raise).  Case 13 gates L46 for a NON-LIST
;;; parameter list (a bare `args', decision D6): it binds nothing.  Case
;;; 14 gates D1 for SEVERAL names after 1 `&optional'.

;; Case 11 -- L45: 1 required name is missing.  C raises
;; `wrong-number-of-arguments' (src/eval.c :2224); this loader binds the
;; elisp nil, so the call answers.
(let* ((def (m19-try (lambda ()
                       (m19-eval '(defun m19-optional-short-required
                                    (a b) (list a b))))))
       (call (m19-try (lambda ()
                        (m19-eval '(m19-optional-short-required 1)))))
       (value (and (eq? 'ok (car call)) (cadr call))))
  (test-assert (format #f "L45 case 11: a missing REQUIRED argument does not raise and binds #nil (call: ~s)"
                       call)
               (and (eq? 'ok (car def))
                    (eq? 'ok (car call))
                    (m19-elems? value '(1 #nil)))))

;; Case 12 -- L45: 1 EXTRA argument.  C raises at :2242; here the extra
;; argument is ignored and the required name keeps the 1st argument.
(let* ((def (m19-try (lambda ()
                       (m19-eval '(defun m19-optional-extra-arg
                                    (a) (list a))))))
       (call (m19-try (lambda ()
                        (m19-eval '(m19-optional-extra-arg 1 2 3)))))
       (value (and (eq? 'ok (car call)) (cadr call))))
  (test-assert (format #f "L45 case 12: an EXTRA argument does not raise and is ignored (call: ~s)"
                       call)
               (and (eq? 'ok (car def))
                    (eq? 'ok (car call))
                    (m19-elems? value '(1)))))

;; Case 13 -- L46 and D6: a NON-LIST parameter list (a bare `args').  The
;; `defun' and the CALL both answer, and the walk binds NOTHING, so the
;; name `args' stays UNBOUND after the call.
(let* ((def (m19-try (lambda ()
                       (m19-eval '(defun m19-optional-bare-params args 42)))))
       (call (m19-try (lambda ()
                        (m19-eval '(m19-optional-bare-params 1 2 3))))))
  (test-assert (format #f "L46 case 13: a non-list parameter list binds nothing and does not raise (def: ~s, call: ~s, args bound: ~s)"
                       def call (symbol-bound? 'args))
               (and (eq? 'ok (car def))
                    (eq? 'ok (car call))
                    (eqv? 42 (cadr call))
                    (not (symbol-bound? 'args)))))

;; Case 14 -- D1 for 2 names after 1 `&optional': every name without an
;; argument binds the elisp nil, and a 4th argument is ignored (L45).
(let* ((def (m19-try (lambda ()
                       (m19-eval '(defun m19-optional-two
                                    (a &optional b c) (list a b c))))))
       (short (m19-try (lambda () (m19-eval '(m19-optional-two 1)))))
       (half (m19-try (lambda () (m19-eval '(m19-optional-two 1 2)))))
       (long (m19-try (lambda () (m19-eval '(m19-optional-two 1 2 3 4))))))
  (test-assert (format #f "L4 case 14: `(a &optional b c)' gives #nil to every name without an argument (1: ~s, 2: ~s, 4: ~s)"
                       short half long)
               (and (eq? 'ok (car def))
                    (eq? 'ok (car short))
                    (m19-elems? (cadr short) '(1 #nil #nil))
                    (eq? 'ok (car half))
                    (m19-elems? (cadr half) '(1 2 #nil))
                    (eq? 'ok (car long))
                    (m19-elems? (cadr long) '(1 2 3)))))

;;; M60 imp-20 -- row 36: the `declare' form is DATA for the byte
;;; compiler.  The loader branch `((eq? head 'declare) #nil)' of
;;; `elisp-loader-eval-form' (mod/emacs/loader.scm) ignores the form and
;;; evaluates NO element.  The C tree owns the name nowhere (0 `defmacro
;;; declare' in lisp/; src/eval.c has no DEFUN and no code branch), so
;;; this is a DECISION, not a port.  The reachable shape is a
;;; DECLARATION BODY FORM of a `defmacro' expander, evaluated at
;;; EXPANSION time.
;;
;; The 7 cases load `standalone-declare.el' ONE time: the argument is
;; not evaluated, the value is the elisp nil, a dotted shape is legal, a
;; body form of an expander is ignored, the load continues, and a
;; declaration in a `defun' body does not raise at CALL time.  `eq?'
;; against #nil is the test, never `null?' or `not': `(eq? #nil '())' is
;; false.
(let* ((load-result (m19-try (lambda ()
                               (load-fixture "standalone-declare.el")
                               'loaded)))
       (loaded (eq? 'loaded (cadr load-result)))
       (empty (and loaded (m19-cell 'm60-declare-empty)))
       (value (and loaded (m19-cell 'm60-declare-value)))
       (dotted (and loaded (m19-cell 'm60-declare-dotted)))
       (expand (and loaded (m19-cell 'm60-declare-expand)))
       (tail (and loaded (m19-cell 'm60-declare-tail)))
       (call (and loaded (m19-cell 'm60-declare-call))))
  ;; Case 1 -- the fixture loads: the top-level `(declare)' does not
  ;; raise on the real load path.
  (test-assert (format #f "row 36 case 1: `standalone-declare.el' loads, so a top-level `(declare)' does not raise (result: ~s)"
                       load-result)
               loaded)
  ;; Case 2 -- 0 arguments are legal and the value is the elisp nil.
  (test-assert (format #f "row 36 case 2: `(declare)' returns the elisp nil (value: ~s, Scheme (): ~s)"
                       empty (and loaded (eq? '() empty)))
               (and loaded (eq? #nil empty)))
  ;; Case 3 -- the argument is NOT evaluated: it names an unbound
  ;; function, and the value is still the elisp nil (L51).
  (test-assert (format #f "row 36 case 3: the argument is not evaluated, although `m60-declare-must-not-run' is unbound (value: ~s, unbound: ~s)"
                       value (not (symbol-fbound? 'm60-declare-must-not-run)))
               (and loaded
                    (eq? #nil value)
                    (not (symbol-fbound? 'm60-declare-must-not-run))))
  ;; Case 4 -- the declaration as the FIRST body form of an expander is
  ;; ignored, and the rest of the body still runs: the expansion is 42.
  (test-assert (format #f "row 36 case 4: a declaration as the first body form of a macro is ignored and the expansion is 42 (value: ~s)"
                       expand)
               (and loaded (eqv? 42 expand)))
  ;; Case 5 -- a DOTTED shape is legal too: the branch reads no element
  ;; of the form, so the value is the elisp nil and nothing raises (L51).
  (test-assert (format #f "row 36 case 5: a dotted `declare' shape returns the elisp nil (value: ~s)"
                       dotted)
               (and loaded (eq? #nil dotted)))
  ;; Case 6 -- the load continues past the forms above.
  (test-assert (format #f "row 36 case 6: the load continues after the declarations (tail: ~s)"
                       tail)
               (and loaded (eq? #t tail)))
  ;; Case 7 -- L14 at CALL time: `lisp/obarray.el' :35 puts the
  ;; declaration in the BODY of a `defun'.  A load does not evaluate a
  ;; body, so the CALL is the shape that must not raise: it answers the
  ;; body value 7.
  (test-assert (format #f "row 36 case 7: a declaration in a `defun' body is data at CALL time and the call answers 7 (value: ~s)"
                       call)
               (and loaded (eqv? 7 call))))

;;; M60 imp-21 -- row 28b: `backquote' is a VALUE BUILDER.  The loader
;;; branch of `elisp-loader-eval-form' (mod/emacs/loader.scm) calls
;;; `elisp-loader-backquote-walk' at depth 1.  The read loop interns the
;;; NAME only, so the head that a real file reaches is the 1-CHARACTER
;;; symbol `(intern "`")' (reader.scm :545); the branch tests both heads.
;;; The C peer interns the NAME only too (`DEFSYM (Qbackquote, "`")',
;;; src/lread.c :3500), so the walk is a DECISION, not a port.
;;
;; The 10 cases load `standalone-backquote.el' ONE time: the top-level
;; backquote does not raise, a `,' at depth 1 evaluates and a `,@' at
;; depth 1 splices, a NESTED backquote keeps its 2 heads at depth 2 (L55),
;; a nested `,@' at depth 2 keeps its structure (L56), a VECTOR argument
;; is walked (F3), the load continues, and `,@' of a non-list raises
;; (L54).  Cases 5 and 8 read TEXT: a Scheme quasiquote can NOT build the
;; 1-character head, so the elisp reader must make the form.
(define m60-backquote-head (string->symbol "`"))
(define m60-unquote-head (string->symbol ","))
(define m60-unquote-spliced-head (string->symbol ",@"))

;; The FIXED expectations of cases 3, 6 and 7, built with `cons' and the
;; elisp nil tail, so a case compares against its OWN value and not
;; against the value that it measures (cr.org F6 of this round).
;; `(a `(b ,m60-bq-c))' -> (a (<bq> (b (<,> m60-bq-c))))
(define m60-bq-nested-want
  (cons 'a
        (cons (cons m60-backquote-head
                    (cons (cons 'b
                                (cons (cons m60-unquote-head
                                            (cons 'm60-bq-c #nil))
                                      #nil))
                          #nil))
              #nil)))
;; `(a `(b ,@m60-bq-c))' -> (a (<bq> (b (<,@> m60-bq-c))))
(define m60-bq-nested-splice-want
  (cons 'a
        (cons (cons m60-backquote-head
                    (cons (cons 'b
                                (cons (cons m60-unquote-spliced-head
                                            (cons 'm60-bq-c #nil))
                                      #nil))
                          #nil))
              #nil)))
;; `(a `(b ,(list 1 2)))' -> (a (<bq> (b (<,> (list 1 2))))).  The
;; argument is a FORM and it is NOT evaluated (L55), and the pair is
;; PROPER: `backquote-delay-process' (:121) listifies the `,' head against
;; the processed cdr, whose value is the LIST (x), so no dotted pair can
;; come out (cr.org F6 of this round).
(define m60-bq-nested-form-want
  (cons 'a
        (cons (cons m60-backquote-head
                    (cons (cons 'b
                                (cons (cons m60-unquote-head
                                            (cons (cons 'list (cons 1 (cons 2 #nil)))
                                                  #nil))
                                      #nil))
                          #nil))
              #nil)))
;; L58: the form `(bq (1 (, m60-bq-b 99)))' built with `cons'.  The walk
;; reads `(cadr form)' only, so the answer is (1 2) and the 99 is DROPPED.
(define m60-bq-multi-form
  (cons m60-backquote-head
        (cons (cons 1 (cons (cons m60-unquote-head
                                  (cons 'm60-bq-b (cons 99 #nil)))
                            #nil))
              #nil)))
;; `[1 ,m60-bq-b ,@m60-bq-c]' -> #[1 2 3 4].  Both unquotes are at depth
;; 1, so the `,' evaluates to 2 and the `,@' spreads 3 and 4.  A vector
;; compare is positional: `(vector-ref v i)'.
(define m60-bq-vector-want #(1 2 3 4))

(let* ((load-result (m19-try (lambda ()
                               (load-fixture "standalone-backquote.el")
                               'loaded)))
       (loaded (eq? 'loaded (cadr load-result)))
       (basic (and loaded (m19-cell 'm60-bq-basic)))
       (nested (and loaded (m19-cell 'm60-bq-nested)))
       (tail (and loaded (m19-cell 'm60-bq-tail)))
       (b (and loaded (m19-cell 'm60-bq-b)))
       (nested-splice (and loaded (m19-cell 'm60-bq-nested-splice)))
       (vector-value (and loaded (m19-cell 'm60-bq-vector)))
       (nested-form (and loaded (m19-cell 'm60-bq-nested-form)))
       (multi-eval (and loaded (m19-try (lambda ()
                                          (m19-eval m60-bq-multi-form)))))
       ;; The inner form of `(a `(b ,m60-bq-c))' is the 2nd element.
       (inner (and loaded (pair? nested) (cadr nested)))
       (inner-arg (and inner (pair? inner) (cadr inner)))
       (comma (and inner-arg (pair? inner-arg) (pair? (cdr inner-arg))
                   (cadr inner-arg)))
       ;; Case 8 reads a `,@' in a VALUE context from TEXT: the whole
       ;; argument of the backquote is the splice.
       (value-splice-form
        (and loaded
             (symbol-fbound? 'read-from-string)
             (m19-try
              (lambda ()
                (car ((symbol-function 'read-from-string)
                      "`,@m60-bq-b"))))))
       (value-splice-eval (and value-splice-form
                               (eq? 'ok (car value-splice-form))
                               (m19-try (lambda ()
                                          (m19-eval (cadr value-splice-form))))))
       ;; Case 5 reads the form from TEXT with the elisp `read-from-string'
       ;; cell (reader.scm :141); it returns (OBJECT . INDEX).
       (splice-form (and loaded
                         (symbol-fbound? 'read-from-string)
                         (m19-try
                          (lambda ()
                            (car ((symbol-function 'read-from-string)
                                  "`(1 ,@m60-bq-b)"))))))
       (splice-eval (and splice-form
                         (eq? 'ok (car splice-form))
                         (m19-try (lambda ()
                                    (m19-eval (cadr splice-form)))))))
  ;; Case 1 -- the fixture loads: a top-level backquote does not raise.
  (test-assert (format #f "row 28b case 1: `standalone-backquote.el' loads, so a top-level backquote does not raise (result: ~s)"
                       load-result)
               loaded)
  ;; Case 2 -- `,' at depth 1 evaluates and `,@' at depth 1 splices the
  ;; ELEMENTS of its proper list.
  (test-assert (format #f "row 28b case 2: ``(1 ,m60-bq-b ,@m60-bq-c 5)' is (1 2 3 4 5) (value: ~s)"
                       basic)
               (and loaded (m19-elems? basic '(1 2 3 4 5))))
  ;; Case 3 -- L55: at depth 2 the `,' is NOT evaluated, so BOTH heads
  ;; survive: the inner pair keeps the 1-character backquote symbol, and
  ;; its argument keeps the `,' symbol with the BARE name after it.  The
  ;; expected value is FIXED, not taken from the value under test (cr.org
  ;; F6 of this round).  A nested structure needs `equal?': `m19-elems?'
  ;; compares the ELEMENTS with `eqv?', and 2 equal pairs are not `eqv?'.
  (test-assert (format #f "row 28b case 3: a nested backquote keeps both heads at depth 2 (nested: ~s, want: ~s)"
                       nested m60-bq-nested-want)
               (and loaded
                    (equal? nested m60-bq-nested-want)
                    (pair? inner)
                    (eq? m60-backquote-head (car inner))
                    (pair? comma)
                    (eq? m60-unquote-head (car comma))
                    (eq? 'm60-bq-c (cadr comma))))
  ;; Case 4 -- the load continues after the forms above.
  (test-assert (format #f "row 28b case 4: the load continues after the backquote forms (tail: ~s)"
                       tail)
               (and loaded (eq? #t tail)))
  ;; Case 5 -- L54: `,@' of the number 2 is not a proper list, so the
  ;; eval RAISES, and `m60-bq-b' is still the number 2.
  (test-assert (format #f "row 28b case 5: `,@' of a non-list raises and names the value (form: ~s, eval: ~s, b: ~s)"
                       splice-form splice-eval b)
               (and splice-form
                    (eq? 'ok (car splice-form))
                    (pair? splice-eval)
                    (eq? 'error (car splice-eval))
                    (eq? 'misc-error (cadr splice-eval))
                    (not (list? b))
                    (eqv? 2 b)))
  ;; Case 6 -- L56: a `,@' at depth 2 keeps its structure and does NOT
  ;; raise.  A full Emacs keeps the same structure by SOURCE
  ;; (lisp/emacs-lisp/backquote.el :166 -> backquote-delay-process :121);
  ;; vanilla Emacs does not run on this host, so this is not a run.
  (test-assert (format #f "row 28b case 6: a nested `,@' at depth 2 keeps its structure (value: ~s, want: ~s)"
                       nested-splice m60-bq-nested-splice-want)
               (and loaded
                    (equal? nested-splice m60-bq-nested-splice-want)))
  ;; Case 7 -- a VECTOR argument is walked: the `,' evaluates and the
  ;; depth-1 `,@' spreads inside the vector.  Before the fix the walk
  ;; returned the vector UNCHANGED and nothing raised (cr.org F3).
  (test-assert (format #f "row 28b case 7: a vector argument is walked, so its unquotes evaluate (vector: ~s, want: ~s)"
                       vector-value m60-bq-vector-want)
               (and loaded
                    (vector? vector-value)
                    (= 4 (vector-length vector-value))
                    (eqv? 1 (vector-ref vector-value 0))
                    (eqv? 2 (vector-ref vector-value 1))
                    (eqv? 3 (vector-ref vector-value 2))
                    (eqv? 4 (vector-ref vector-value 3))))
  ;; Case 8 -- L56: a `,@' as the WHOLE argument of a backquote is a VALUE
  ;; context at depth 1, so the eval RAISES (cr.org F8 of this round).
  (test-assert (format #f "row 28b case 8: a `,@' in a value context raises (form: ~s, eval: ~s)"
                       value-splice-form value-splice-eval)
               (and value-splice-form
                    (eq? 'ok (car value-splice-form))
                    (pair? value-splice-eval)
                    (eq? 'error (car value-splice-eval))
                    (eq? 'misc-error (cadr value-splice-eval))))
  ;; Case 9 -- the SHAPE of a DELAYED unquote with a COMPOUND argument:
  ;; the argument is a FORM and it is not evaluated, and the pair is
  ;; proper (cr.org F6 of this round).  The expected value is FIXED.
  (test-assert (format #f "row 28b case 9: a delayed unquote keeps its argument as a FORM in a proper pair (value: ~s, want: ~s)"
                       nested-form m60-bq-nested-form-want)
               (and loaded
                    (equal? nested-form m60-bq-nested-form-want)))
  ;; Case 10 -- L58: an unquote with 2 arguments does not raise here and
  ;; the FIRST argument wins (cr.org F8 of this round).
  (test-assert (format #f "row 28b case 10: L58 an unquote with 2 arguments answers (1 2) and drops the 2nd (eval: ~s)"
                       multi-eval)
               (and loaded
                    (pair? multi-eval)
                    (eq? 'ok (car multi-eval))
                    (m19-elems? (cadr multi-eval) '(1 2)))))

;;; M60 imp-22 -- row 37: the `purecopy' cell of (emacs types) :439,
;;; installed by the guarded block of `init-loader'.  The C owner is
;;; `Fpurecopy' (src/alloc.c :1513), its body is `return obj;', and its
;;; argument vector 1, 1, 0 names NO type predicate, so NO argument
;;; raises.  Limit L59: a MUTABLE object comes back as the SAME object.

;; Case 1 -- the CELL is present after `init-loader' and holds a
;; PROCEDURE.  The `procedure?' arm is the observable of brief.org
;; section 4.1: a stub VALUE in the cell must NOT pass this case
;; (cr.org F3 of the imp-22 review).
(let ((cell (and (symbol-fbound? 'purecopy) (symbol-function 'purecopy))))
  (test-assert (format #f "row 37: `init-loader' installs the `purecopy' cell as a PROCEDURE (fbound: ~s, procedure: ~s)"
                       (symbol-fbound? 'purecopy)
                       (and cell (procedure? cell)))
               (and (eq? #t (symbol-fbound? 'purecopy))
                    (procedure? cell))))

;; Case 2 -- the CELL is the IDENTITY for a symbol and for an integer,
;; and no argument raises.
(let* ((cell (and (symbol-fbound? 'purecopy) (symbol-function 'purecopy)))
       (sym (and cell (apply cell '(m60-imp22))))
       (num (and cell
                 (catch #t
                   (lambda () (list 'ok (apply cell '(42))))
                   (lambda (key . args) (cons 'error (cons key args)))))))
  (test-assert (format #f "row 37: the installed `purecopy' cell returns the SAME symbol and an integer unchanged, with no raise (sym: ~s, num: ~s)"
                       sym num)
               (and (eq? sym 'm60-imp22) (equal? num '(ok 42)))))

;; Case 3 -- the elisp nil stays `#nil'.  `equal?' keeps the 3 truth
;; values apart, so a cell that answers `#f' gives `(ok #f)' and FAILS
;; here.  The OLD form `(not (eq? #nil #f))' is deleted: it is a
;; CONSTANT and proves nothing at any run (cr.org F6 of the imp-22
;; review).
(let ((result (and (symbol-fbound? 'purecopy)
                   (catch #t
                     (lambda ()
                       (list 'ok (apply (symbol-function 'purecopy)
                                        (list #nil))))
                     (lambda (key . args) (cons 'error (cons key args)))))))
  (test-assert (format #f "row 37: the elisp nil passes through the installed `purecopy' cell unchanged (result: ~s)"
                       result)
               (equal? result (list 'ok #nil))))

;; Case 4 -- a STRING comes back as the SAME object (`eq?').  This is
;; limit L59: a dumping build answers a COPY, because `make_pure_c_string'
;; (:1502) cannot look through the call here.
(let* ((cell (and (symbol-fbound? 'purecopy) (symbol-function 'purecopy)))
       (str (and cell (string-copy "m60-imp22-string")))
       (back (and str (apply cell (list str)))))
  (test-assert (format #f "row 37: a string comes back as the SAME object (back: ~s)"
                       back)
               (and (string? back) (eq? str back))))

;; Case 5 -- a CONS comes back as the SAME cons, so a later `set-car!'
;; on the answer is visible to the caller.  L59 pins this; it is not a
;; defect of the port.
(let* ((cell (and (symbol-fbound? 'purecopy) (symbol-function 'purecopy)))
       (obj (and cell (list 1 2)))
       (back (and obj (apply cell (list obj)))))
  (when (and back (pair? back)) (set-car! back 'm60-imp22-mutated))
  (test-assert (format #f "row 37: a cons comes back as the SAME cons and `set-car!' is visible to the caller (obj: ~s)"
                       obj)
               (and (pair? back)
                    (eq? obj back)
                    (eq? 'm60-imp22-mutated (car obj)))))

;; Case 6 -- `standalone-purecopy.el' loads: its macro expander body
;; calls the cell at LOAD time, so a missing cell fails the load.
(let ((result (catch #t
                (lambda () (load-fixture "standalone-purecopy.el") 'loaded)
                (lambda (key . args) (cons 'error (cons key args))))))
  (test-assert (format #f "row 37: `standalone-purecopy.el' loads with `purecopy' in an expander body (result: ~s)"
                       result)
               (eq? 'loaded result)))

;; Case 7 -- the stored values of the fixture: the macro expansion is the
;; quoted symbol, the integer is unchanged, and the load reached the END
;; (the tail cell is set).
(test-assert (format #f "row 37: the fixture keeps the identity answers and reaches its tail (expanded: ~s, string: ~s, integer: ~s, tail: ~s)"
                     (and (symbol-bound? 'm60-purecopy-expanded)
                          (symbol-value 'm60-purecopy-expanded))
                     (and (symbol-bound? 'm60-purecopy-string)
                          (symbol-value 'm60-purecopy-string))
                     (and (symbol-bound? 'm60-purecopy-integer)
                          (symbol-value 'm60-purecopy-integer))
                     (and (symbol-bound? 'm60-purecopy-tail)
                          (symbol-value 'm60-purecopy-tail)))
             (and (symbol-bound? 'm60-purecopy-expanded)
                  (eq? 'm60-purecopy-value
                       (symbol-value 'm60-purecopy-expanded))
                  (symbol-bound? 'm60-purecopy-string)
                  (equal? "m60-purecopy-string"
                          (symbol-value 'm60-purecopy-string))
                  (symbol-bound? 'm60-purecopy-integer)
                  (equal? 42 (symbol-value 'm60-purecopy-integer))
                  (symbol-bound? 'm60-purecopy-tail)
                  (eq? #t (symbol-value 'm60-purecopy-tail))))

;; Case 8 -- an AGGREGATE object comes back as the SAME object.  The C
;; body is `return obj;', so the identity holds for a vector and for a
;; hash table too.  cr.org section 5 of the imp-22 review left this type
;; NOT measured.
(let* ((cell (and (symbol-fbound? 'purecopy) (symbol-function 'purecopy)))
       (vec (and cell (vector 1 2 3)))
       (tbl (and cell (make-hash-table))))
  (test-assert (format #f "row 37: an aggregate object (a vector, a hash table) comes back as the SAME object (vec: ~s, tbl: ~s)"
                       vec tbl)
               (and (vector? vec)
                    (eq? vec (apply cell (list vec)))
                    (hash-table? tbl)
                    (eq? tbl (apply cell (list tbl))))))

(test-end "Guilemacs standalone loader and reader")

(let ((passes (test-runner-pass-count test-runner))
      (fails  (test-runner-fail-count test-runner)))
  (format #t "~a: ~a passed, ~a failed (expected ~a passed)~%"
          "Guilemacs standalone loader and reader" passes fails
          expected-passes)
  (exit (if (and (zero? fails) (= passes expected-passes)) 0 1)))
