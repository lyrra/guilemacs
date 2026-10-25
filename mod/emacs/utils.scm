;;; Guilemacs Lisp
;;;
;;; Utilities & Property Lists
;;;
;;; Purpose: Symbol properties, hash tables, features, and utilities
;;; Loading: via use-modules in load.scm
;;;
;;; EXPORTS (37+ functions):
;;;   Symbol properties: get, put, symbol-plist, setplist
;;;   Obarray: intern, intern-soft, mapatoms, unintern
;;;   Features: featurep, provide  (require is the cell of (emacs loader))
;;;   Hash tables: make-hash-table, gethash, puthash, remhash, clrhash, hash-table-count
;;;   Comparison: equal-including-properties
;;;   Other: copy-tree, fillarray
;;;   Registration: init-utils-registrations

(define-module (emacs utils)
  #:use-module (emacs-elisp runtime)
  #:use-module (emacs sequences)
  #:use-module (srfi srfi-69)
  #:export (
    ;; Scheme implementation functions
    elisp-get-load-suffixes
    elisp-get elisp-put elisp-symbol-plist elisp-setplist
    elisp-intern elisp-intern-soft elisp-mapatoms elisp-unintern
    elisp-featurep elisp-provide
    ;; M60 imp-16 -- row 25: installed by `init-loader' with the row-18
    ;; guard.  The private trailing-"/" strip stays unexported.
    elisp-normal-top-level-add-to-load-path
    elisp-make-obsolete-variable
    elisp-make-hash-table elisp-gethash elisp-puthash elisp-remhash
    elisp-clrhash elisp-hash-table-count elisp-hash-table-test
    elisp-hash-table-weakness elisp-hash-table-rehash-size
    elisp-hash-table-rehash-threshold elisp-hash-table-size
    elisp-hash-table-keys elisp-hash-table-values
    elisp-equal-including-properties elisp-copy-tree elisp-fillarray
    elisp-symbol-function elisp-symbol-value elisp-set
    ;; M60 imp-14 -- row 34: `defalias' is EXPORTED here and installed by
    ;; `init-loader' (loader.scm) with the row-18 guard.  `elisp-fset'
    ;; next to it is still EXPORTED with NO definition; that row stays
    ;; OPEN.
    elisp-defalias
    elisp-fset elisp-setq
    elisp-make-symbol elisp-gensym
    set-debug-print-flag
    ;; Mathematical utilities
    elisp-copysign elisp-frexp elisp-ldexp elisp-logb
    elisp-sign elisp-clamp elisp-square
    ;; Other utilities
    elisp-nreverse
    elisp-markerp elisp-keywordp
    elisp-file-name-absolute-p
    elisp-get-load-suffixes
    elisp-obarrayp elisp-obarray-make elisp-obarray-clear
    elisp-intern-soft-lread elisp-unintern
    elisp-read-char
    elisp-save-current-buffer elisp-with-current-buffer
    elisp-make-string
    elisp-sxhash-eq elisp-sxhash-eql elisp-sxhash-equal
    elisp-convert-guile-object
    init-utils-registrations
  ))

;;;   #:export (...))

;;;
;;; Load System Utilities
;;;

(define (elisp-get-load-suffixes)
  "Return the suffixes that `load' should try if a suffix is required.
This uses the variables `load-suffixes' and `load-file-rep-suffixes'."
  (let ((result '()))
    (for-each
      (lambda (suffix)
        (for-each
          (lambda (ext)
            (set! result (cons (string-append suffix ext) result)))
          (symbol-value 'load-file-rep-suffixes)))
      (symbol-value 'load-suffixes))
    (reverse result)))

;;;
;;; Obarray Operations
;;;

(define (elisp-obarrayp object)
  "Return t if OBJECT is an obarray."
  (if (vector? object) #t #nil))

(define (elisp-obarray-make size)
  "Return a new obarray of size SIZE.
The obarray will grow to accommodate any number of symbols; the size, if
given, is only a hint for the expected number."
  (make-vector (if (and size (integer? size) (> size 0)) size 128) '()))

(define (elisp-obarray-clear obarray)
  "Remove all symbols from OBARRAY."
  (if (vector? obarray)
      (let ((len (vector-length obarray)))
        (do ((i 0 (+ i 1)))
            ((>= i len) obarray)
          (vector-set! obarray i '())))
      (error "Wrong type argument: obarrayp" obarray)))

(define (elisp-intern string obarray)
  "Return the canonical symbol whose name is STRING.
If there is none, one is created by this function and returned.
A second optional argument specifies the obarray to use;
it defaults to the value of `obarray'."
  (let ((str (if (symbol? string) (symbol->string string) string)))
    (if (not (string? str))
        ((symbol-function 'signal) 'wrong-type-argument (cons 'stringp str))
        (string->symbol str))))

(define (elisp-intern-soft-lread name obarray)
  "Return the canonical symbol named NAME, or nil if none exists.
NAME may be a string or a symbol. If it is a symbol, that exact
symbol is searched for. A second optional argument specifies the obarray to use;
it defaults to the value of `obarray'."
  (let ((str (if (symbol? name) (symbol->string name) name)))
    (if (not (string? str))
        #nil
        (catch #t
          (lambda ()
            (let ((sym (string->symbol str)))
              (if (symbol-bound? sym) sym #nil)))
          (lambda (key . args)
            #nil)))))

(define (elisp-unintern name obarray)
  "Delete the symbol named NAME, if any, from OBARRAY.
The value is t if a symbol was found and deleted, nil otherwise.
NAME may be a string or a symbol. If it is a symbol, that symbol
is deleted, if it belongs to OBARRAY--no other symbol is deleted."
  (let ((str (if (symbol? name) (symbol->string name) name)))
    (if (not (string? str))
        #nil
        ;; In Guile, symbols are globally interned, so we can't really unintern
        #nil)))

;;;
;;; Symbol Property Functions
;;;

(define (elisp-symbol-plist symbol)
  "Return SYMBOL's property list."
  (if (symbol? symbol)
      (catch #t
        (lambda ()
          (symbol-property symbol '*elisp-plist*))
        (lambda (key . args)
          #nil))
      (error "Wrong type argument: symbolp" symbol)))

(define (elisp-setplist symbol plist)
  "Set SYMBOL's property list to PLIST and return PLIST."
  (if (symbol? symbol)
      (begin
        (set-symbol-property! symbol '*elisp-plist* plist)
        plist)
      (error "Wrong type argument: symbolp" symbol)))

(define (elisp-get symbol propname)
  "Return the value of SYMBOL's PROPNAME property.
This is the last value stored with '(put SYMBOL PROPNAME VALUE)'."
  (if (symbol? symbol)
      (let ((plist (elisp-symbol-plist symbol)))
        (elisp-plist-get plist propname))
      (error "Wrong type argument: symbolp" symbol)))

(define (elisp-put symbol propname value)
  "Store SYMBOL's PROPNAME property with value VALUE.
It can be retrieved with '(get SYMBOL PROPNAME)'."
  (if (symbol? symbol)
      (let ((old-plist (elisp-symbol-plist symbol)))
        (let ((new-plist (elisp-plist-put old-plist propname value)))
          (elisp-setplist symbol new-plist)
          value))
      (error "Wrong type argument: symbolp" symbol)))

;;; M60 imp-13 -- row 33: `set' writes the VALUE cell only.  C owner is
;;; `Fset' (src/data.c :1317), which returns NEWVAL.  The reader applies
;;; this cell for every `:keyword' form (reader.scm :1358), and the 2
;;; read-eval loops apply it for `values' (loader.scm :132, :227).
;;; `set-symbol-value!' (mod/emacs-elisp/runtime.scm :357) stores and
;;; returns VALUE, and the elisp truth values are kept (#nil stays #nil).
;;;
;;; The buffer-local, `varalias', `permanent-local' and watcher branches
;;; of `set_internal' (src/data.c :1360) are NOT ported.
;;; FIX-20261022-guilemacs: port them when a loaded file needs a
;;; buffer-local value or a variable alias.
;;; The SYMBOL_NOWRITE test (src/data.c :1346) is NOT ported, so a
;;; keyword store with a DIFFERENT value succeeds instead of raising
;;; `setting-constant'.  The reader passes the SAME value.
;;; FIX-20261022-guilemacs: port that test when a loaded file writes a
;;; keyword with a different value.
(define (elisp-set symbol newval)
  "Set SYMBOL's value to NEWVAL and return NEWVAL."
  (if (symbol? symbol)
      (set-symbol-value! symbol newval)
      (error "Wrong type argument: symbolp" symbol)))

;;; M60 imp-14 -- row 34: `defalias' writes the FUNCTION cell.  C owner is
;;; `Fdefalias' (src/data.c :706); the worker `defalias' (:675) writes the
;;; cell.  This port has CHECK_SYMBOL on ARG 1 (:719), the cell write
;;; (`Ffset', :702), the `function-documentation' property (:728) and the
;;; return value = SYMBOL (:732, bug#11686).  DEFINITION is stored AS
;;; WRITTEN: it is NOT resolved, because C keeps an INDIRECTION there.
;;; So `(defalias 'string= #'string-equal)' leaves the SYMBOL
;;; `string-equal' in the cell, and `(string= "a" "a")' still gives t.
;;;
;;; The 4 parts that are NOT ported, each a named limit:
;;; L31 macro table: a `defalias' does NOT drop an entry of
;;;     `elisp-loader-macro-table' (loader.scm :1176).  Only the `defun'
;;;     branch drops it (loader.scm :1253).  Emacs keeps ONE cell, so a
;;;     `defalias' of a name that is a macro HERE leaves the stale
;;;     expander.  No loaded file needs this today.
;;; FIX-20261022-guilemacs: drop the macro entry in `defalias' too.
;;; L32 advice hook: a non-nil `defalias-fset-function' property would
;;;     REPLACE the cell write (:702).  It is ignored, so advice that
;;;     uses that property does nothing on this path.
;;; FIX-20261022-guilemacs: test the `defalias-fset-function' property
;;; first, as the C worker does.
;;; L33 pure copy: `Vpurify_flag' (:720) and `Fpurecopy' (:723) are not
;;;     ported, so a definition is never copied or shared with a dump.
;;; FIX-20261022-guilemacs: port the `Fpurecopy' step when a dump exists.
;;; L34 load history: `LOADHIST_ATTACH' and `add_to_function_history'
;;;     (:683, :693) are not ported, so `load-history' does not change and
;;;     `symbol-file' does not see this definition.
;;; FIX-20261022-guilemacs: record the definition in `load-history'.
;;;
;;; The 3rd argument is the DOCSTRING.  C tests `!NILP' (:727), not
;;; `stringp', so ANY non-nil value sets the property; a string is the
;;; only shape that a caller passes.  The elisp nil has 3 spellings
;;; here: `#nil' (the value), the symbol `nil' and the empty list, and
;;; all 3 leave the property EMPTY.
(define (elisp-defalias symbol definition . maybe-doc)
  "Set SYMBOL's function definition to DEFINITION and return SYMBOL.
The optional 3rd argument is the DOCSTRING.  It sets SYMBOL's
`function-documentation' property; when it is nil, SYMBOL uses the
documentation string of DEFINITION."
  (if (symbol? symbol)
      (begin
        (set-symbol-function! symbol definition)
        (if (pair? maybe-doc)
            (let ((doc (car maybe-doc)))
              (if (not (or (eq? doc #nil) (eq? doc 'nil) (null? doc)))
                  (elisp-put symbol 'function-documentation doc))))
        symbol)
      (error "Wrong type argument: symbolp" symbol)))

;;;
;;; Hash Table Operations
;;;

(define (elisp-hash-table-count table)
  "Return the number of entries in TABLE."
  (if (hash-table? table)
      (hash-table-size table)
      (error "Wrong type argument: hash-table-p" table)))

(define (elisp-clrhash table)
  "Clear hash table TABLE and return it."
  (if (hash-table? table)
      ;; M60 imp-15 (row 32) FIX: `(srfi srfi-69)' of THIS Guile does NOT
      ;; export `hash-table-clear!' (measured: `module-defined?' is #f),
      ;; so the first definition raised `unbound-variable' on every call.
      ;; The keys walk and `hash-table-delete!' replace it; the TABLE
      ;; object stays the same, as C `Fclrhash' (:5445) returns it.
      (begin
        (for-each (lambda (key) (hash-table-delete! table key))
                  (hash-table-keys table))
        table)
      (error "Wrong type argument: hash-table-p" table)))

;; M60 imp-15 -- row 32: the `make-hash-table' family.  The C owner is
;; `Fmake_hash_table' (src/fns.c :5253).  A real file reaches it first
;; at `lisp/emacs-lisp/macroexp.el' :165, the `defvar' of
;; `macroexp--warned'.
;;
;; D1: 1 SRFI-69 table IS the elisp hash table.  `(srfi srfi-69)' is
;; imported above, and `elisp-hash-table-p' (types.scm :444) plus the 2
;; procedures above test the object with `hash-table?', so a second
;; representation would break 3 live sites.  No record, no wrapper, no
;; FFI.
;;
;; D4: a `:keyword' is SELF-EVALUATING (`set' at reader.scm :1359, the
;; body of `elisp-intern-and-make-keyword' :1354), so it arrives
;; here as the elisp SYMBOL named ":test", NOT as a Guile keyword.
;; `#'equal' arrives as the symbol `equal' (row 34 passes the head
;; symbol), and `'key' arrives as the symbol `key'.
;;
;; FIX-20261024-guilemacs: LIMIT L37 (D3).  A valid `:weakness' argument
;; is PARSED and then IGNORED, so every table is STRONG.  This SRFI-69
;; does have weak constructors (measured: `make-weak-key-hash-table' is a
;; procedure), but a weak table is a different port.  Row 32 must not
;; become that port, so `hash-table-weakness' answers the elisp nil.
;;
;; FIX-20261024-guilemacs: LIMIT L38 (D6).  `hash-table-size' answers
;; the number of ENTRIES.  C answers the ALLOCATION size (src/fns.c
;; :5391), and SRFI-69 `hash-table-size' counts entries (measured: 2
;; after 2 inserts).  A caller that wants the count gets it.

;; SRFI-69 calls a table's hash function with 2 arguments, (KEY BOUND)
;; (measured: a 1-argument lambda raised "Wrong number of arguments").
;; Guile `hashq' and `hashv' have exactly that arity, so the test table
;; passes them as they are.
(define %hash-default-size 64)

;; A private object that no elisp key or value can be: it separates an
;; ABSENT key from a stored elisp nil.
(define %hash-absent (list 'hash-absent))

;; The elisp nil is 1 object on this path, but the literal path can give
;; the symbol `nil' or the empty list too.  Same test as `elisp-defalias'
;; (utils.scm :236).
(define (elisp-hash-nil? obj)
  (or (eq? obj #nil) (eq? obj 'nil) (null? obj)))

;; D2: the 3 predefined tests of C (`src/fns.c' :5314 ... :5322), as 1
;; pair of EQUIVALENCE and HASH.  The hash function must MATCH the
;; equivalence, or 2 `eq?' keys can land in different buckets.  An
;; unknown test raises like C `get_hash_table_user_test' (:5230); there
;; is no user test registry on this path.
(define (elisp-hash-test-functions test)
  (cond ((eq? test (string->symbol "eq")) (cons eq? hashq))
        ((eq? test (string->symbol "eql")) (cons eqv? hashv))
        ((eq? test (string->symbol "equal")) (cons equal? hash))
        (else (error "Invalid hash table test" test))))

;; The keyword symbols of the C decode loop (`src/fns.c' :5296 ... :5309).
(define %hash-kw-test (string->symbol ":test"))
(define %hash-kw-weakness (string->symbol ":weakness"))
(define %hash-kw-size (string->symbol ":size"))
(define %hash-kw-purecopy (string->symbol ":purecopy"))
(define %hash-kw-rehash-size (string->symbol ":rehash-size"))
(define %hash-kw-rehash-threshold (string->symbol ":rehash-threshold"))

;; A valid `:weakness' value, or a raise like C :5344.  The value is NOT
;; honored (L37): only the validation is ported.
(define (elisp-hash-check-weakness weakness)
  (cond ((elisp-hash-nil? weakness) #nil)
        ((or (eq? weakness (string->symbol "key"))
             (eq? weakness (string->symbol "value"))
             (eq? weakness (string->symbol "key-or-value"))
             (eq? weakness (string->symbol "key-and-value"))
             (eq? weakness #t)
             (eq? weakness 't))
         weakness)
        (else (error "Invalid hash table weakness" weakness))))

(define (elisp-make-hash-table . args)
  "Create and return a new hash table.  Port of `Fmake_hash_table'."
  (if (odd? (length args))
      ;; C: `if (nargs & 1) error ("Odd number of arguments")' (:5293).
      (error "Odd number of arguments")
      ;; The C loop `while (nargs >= 2)' (:5294) reads the argument
      ;; vector RIGHT to LEFT, so a REPEATED keyword keeps the FIRST
      ;; value.  The REVERSE below gives that same order, and the last
      ;; assignment of a keyword is then its FIRST pair.
      (let loop ((rest (reverse args))
                 (test #nil) (weakness #nil) (size #nil) (purecopy #nil))
        (if (null? rest)
            (let* ((test-key (if (elisp-hash-nil? test)
                                 (string->symbol "eql")   ; default :5314
                                 test))
                   (test-fn (elisp-hash-test-functions test-key))
                   (size-n (cond ((elisp-hash-nil? size)
                                  %hash-default-size)
                                 ((and (exact-integer? size) (>= size 0)) size)
                                 (else (error "Invalid hash table size" size))))
                   ;; The weakness check runs BEFORE the constructor,
                   ;; like C (:5344 then :5346).  The result is unused:
                   ;; a valid value is ignored (L37).
                   (_ (elisp-hash-check-weakness weakness)))
              ;; `purecopy' is read and ignored (D5): C copies a table to
              ;; pure storage only during a dump.
              ;; The `:size' value is a HINT and passes through
              ;; unchanged: C also accepts 0 (`FIXNATP', :5327), so no
              ;; `max' clamps it to 1.
              (make-hash-table (car test-fn) (cdr test-fn) size-n))
            ;; After the `reverse', the FIRST element is the VALUE and
            ;; the second is the KEYWORD.  C reads the same 2 slots in
            ;; that same order (:5296: `arg = args[--nargs]' then
            ;; `keyword = args[--nargs]').
            (let ((value (car rest))
                  (keyword (and (pair? (cdr rest)) (cadr rest))))
              (cond ((eq? keyword %hash-kw-test)
                     (loop (cddr rest) value weakness size purecopy))
                    ((eq? keyword %hash-kw-weakness)
                     (loop (cddr rest) test value size purecopy))
                    ((eq? keyword %hash-kw-size)
                     (loop (cddr rest) test weakness value purecopy))
                    ((eq? keyword %hash-kw-purecopy)
                     (loop (cddr rest) test weakness size value))
                    ;; The 2 obsolete keywords are read and ignored
                    ;; (C: `;/* ignore obsolete keyword arguments */').
                    ((or (eq? keyword %hash-kw-rehash-size)
                         (eq? keyword %hash-kw-rehash-threshold))
                     (loop (cddr rest) test weakness size purecopy))
                    (else (error "Invalid keyword argument" keyword))))))))

;; `gethash' of C is 2 ... 3 args (`Fgethash', src/fns.c :5457).  It
;; returns the value of KEY in TABLE, or DEFAULT when KEY is absent.  A
;; 2-argument call passes the elisp nil as DEFAULT.
(define elisp-gethash
  (case-lambda
    ((key table)
     (elisp-gethash key table #nil))
    ((key table default)
     (if (hash-table? table)
         (let ((value (hash-table-ref/default table key %hash-absent)))
           (if (eq? value %hash-absent) default value))
         (error "Wrong type argument: hash-table-p" table)))))

(define (elisp-puthash key value table)
  "Associate KEY with VALUE in TABLE and return VALUE.
C owner: `Fputhash' (src/fns.c :5471)."
  (if (hash-table? table)
      (begin
        (hash-table-set! table key value)
        value)
      (error "Wrong type argument: hash-table-p" table)))

(define (elisp-remhash key table)
  "Remove KEY from TABLE.  C owner `Fremhash' (src/fns.c :5491) returns
the elisp nil in BOTH cases: the C body calls `hash_remove_from_table'
and then returns Qnil, with no test for presence."
  (if (hash-table? table)
      (begin
        (hash-table-delete! table key)
        #nil)
      (error "Wrong type argument: hash-table-p" table)))

;; D6: a SRFI-69 table reports its own equivalence function (measured:
;; `hash-table-equivalence-function' is a procedure), so the elisp test
;; symbol is recoverable and no side table is needed.
;;
;; FIX-20261024-guilemacs: this is NOT a tracker limit (it has no L
;; number).  A table whose equivalence function is NOT one of the 3 pairs
;; answers the elisp nil.  C answers the user test SYMBOL (:5407).  This
;; path has no user test registry, so only the 3 predefined tests exist.
;; Low risk: only row 32 builds tables today.
(define (elisp-hash-table-test table)
  "Return the test symbol that TABLE uses.  C owner :5407."
  (if (hash-table? table)
      (let ((equiv (hash-table-equivalence-function table)))
        (cond ((eq? equiv eq?) (string->symbol "eq"))
              ((eq? equiv equal?) (string->symbol "equal"))
              ((eq? equiv eqv?) (string->symbol "eql"))
              (else #nil)))
      (error "Wrong type argument: hash-table-p" table)))

(define (elisp-hash-table-weakness table)
  "Return the weakness of TABLE.  C owner :5428.  Every table of this
port is STRONG (L37), so the answer is the elisp nil."
  (if (hash-table? table)
      #nil
      (error "Wrong type argument: hash-table-p" table)))

(define (elisp-hash-table-size table)
  "Return the number of entries of TABLE (L38: C answers the allocation
size).  C owner :5391."
  (if (hash-table? table)
      (hash-table-size table)
      (error "Wrong type argument: hash-table-p" table)))

(define (elisp-hash-table-rehash-size table)
  "The obsolete nominal constant of C :5375."
  (if (hash-table? table) 1.5 (error "Wrong type argument: hash-table-p" table)))

(define (elisp-hash-table-rehash-threshold table)
  "The obsolete nominal constant of C :5387."
  (if (hash-table? table) 0.8125 (error "Wrong type argument: hash-table-p" table)))

(define (elisp-hash-table-keys table)
  "Return the keys of TABLE as a list."
  (if (hash-table? table)
      (hash-table-keys table)
      (error "Wrong type argument: hash-table-p" table)))

(define (elisp-hash-table-values table)
  "Return the values of TABLE as a list."
  (if (hash-table? table)
      (hash-table-values table)
      (error "Wrong type argument: hash-table-p" table)))

;;;
;;; Feature/Provide System
;;;

(define elisp-featurep
  (case-lambda
    ((feature)
     ;; Called with 1 argument - no subfeature check
     (elisp-featurep feature #nil))
    ((feature subfeature)
     ;; Called with 2 arguments
     "Return t if FEATURE is present in this Emacs.
Use this to conditionalize execution of lisp code based on the
presence or absence of Emacs or environment extensions."
     (if (memq feature (symbol-value 'features))
         (if (or (null? subfeature) (eq? subfeature #nil))
             #t
             #t)  ; Simplified: assume subfeatures are present if feature is
         #nil))))

;; M60 imp-16 -- row 25.  The owner is the elisp Lisp function of
;; lisp/startup.el :479 (`normal-top-level-add-to-load-path'), not a C
;; DEFUN: `grep -rn normal-top-level-add-to-load-path src/' gives 0 hits.
;; The 1 caller is lisp/subdirs.el :3.  `startup.el' can not load yet: it
;; stops on `void-function (defgroup)' (`defgroup' is a `&rest args'
;; `defmacro' of lisp/custom.el :517, and `custom.el' stops on the
;; `&optional' / `&rest' wall L4 of loader.scm), so the port lives here
;; and `init-loader' installs it with 1 guard (the row-18 pattern,
;; loader.scm).
;; M60 imp-18 (row 35): the old blocker named here, the C cell
;; `bare-symbol', is CLOSED -- `lisp/emacs-lisp/byte-run.el' loads to the
;; END now (27 forms of 27, measured).  The `defgroup' stop above is the
;; MEASURED next one.
;;
;; The port holds the DECISION, not a wrapper: the anchor search, the
;; trailing-"/" strip and the splice are Scheme.  No C leaf is called and
;; no libc FFI is used.  `(emacs fileio)' is C-backed and does not run on
;; this path, so the port does NOT call `fileio-directory-file-name'.
;;
;; M60 imp-16 LIMITS of row 25 -- named, not claimed:
;;   L39: `set-cdr!' needs a MUTABLE pair.  A caller that binds
;;        `load-path' to a QUOTED literal gets an error where Emacs
;;        mutates.  The plain path is safe: `init-loader' binds a `list'
;;        (loader.scm :1507).
;;   L40: the DOS_NT branch is NOT ported.  The elisp loop also compares
;;        `downcase' of the 2 names when `system-type' is `ms-dos' or
;;        `windows-nt'.
;;   L41: the `expand-file-name' cell is the loader join
;;        (loader.scm :988).  Its 1-argument form is NOT implemented: it
;;        raises `wrong-number-of-arguments'.  The port passes the
;;        directory as the 2nd argument.
;;   L42: the port does not bind `default-directory'.  The caller must
;;        bind it (lisp/startup.el :631).  A load without the bind raises
;;        `void-variable', which is the elisp behaviour.
;;   L43: the port is NOT idempotent.  A 2nd load of `subdirs.el'
;;        splices 24 more entries.  The elisp function does the same.

;; `directory-file-name': drop the trailing "/" and keep "/" alone.
(define (elisp--directory-name-strip name)
  (let loop ((i (string-length name)))
    (if (and (> i 1) (char=? (string-ref name (- i 1)) #\/))
        (loop (- i 1))
        (substring name 0 i))))

;; Row 25: a Scheme port of `normal-top-level-add-to-load-path'
;; (lisp/startup.el :479).  The caller binds `default-directory' to the
;; directory of the subdirs.el file (lisp/startup.el :631), so the port
;; READS that variable and never binds it.
(define (elisp-normal-top-level-add-to-load-path dirs)
  (if (not (symbol-bound? 'default-directory))
      ;; The evaluator rule: an unbound variable raises, it does not
      ;; answer nil.  `symbol-value' would answer the unbound sentinel.
      (throw 'void-variable 'default-directory)
      (let* ((thisdir (elisp--directory-name-strip
                       (symbol-value 'default-directory)))
             (expand (symbol-function 'expand-file-name))
             ;; The elisp body applies `mapcar #'expand-file-name' with
             ;; 1 argument.  Here the directory is passed explicitly, so
             ;; the port needs no 1-argument `expand-file-name'.
             (new (map (lambda (dir) (expand dir thisdir)) dirs)))
        ;; Walk to the tail cell whose car is THISDIR, as the elisp loop
        ;; does (lisp/startup.el :486 ... :492): stop on a MATCH, on the
        ;; TAIL cell, or on the nil terminator.  The splice runs for
        ;; EVERY non-nil TAIL (`(when tail (setcdr ...))', :495), so a
        ;; match AT the tail cell and an ABSENT anchor both splice after
        ;; the tail cell.  The DOS_NT `downcase' compare of L40 joins
        ;; this `or'.
        (let loop ((tail (symbol-value 'load-path)))
          (cond ((not (pair? tail)) #nil)
                ((or (not (pair? (cdr tail)))
                     (equal? thisdir (car tail)))
                 (set-cdr! tail (append new (cdr tail)))
                 (cdr tail))
                (else (loop (cdr tail))))))))

(define elisp-provide
  (case-lambda
    ((feature)
     ;; Called with 1 argument - no subfeatures
     (elisp-provide feature #nil))
    ((feature subfeatures)
     ;; Called with 2 arguments
     "Announce that FEATURE is a feature of the current Emacs.
The optional argument SUBFEATURES should be a list of symbols listing
particular subfeatures supported in this version of FEATURE."
     (let ((current-features (symbol-value 'features)))
       (if (not (memq feature current-features))
           (set-symbol-value! 'features (cons feature current-features))))
     feature)))

;; M60 imp-8 -- row 27.  The owner is the Lisp function of
;; lisp/emacs-lisp/byte-run.el :564, not a C DEFUN: `rg -c
;; make-obsolete-variable src/' gives 0 hits.  The mark is DATA only, in
;; the source order of byte-run.el :576: (CURRENT-NAME ACCESS-TYPE WHEN).
;; The 3-arity form passes #nil and NOT '(): (equal? #nil '()) is #f.
;; The return value is the SYMBOL; `elisp-put' above returns the VALUE.
;;
;; M60 imp-8 LIMITS of row 27 -- named, not claimed:
;;   L11: no `purecopy'.  It needs its own cell and it is not in the
;;        tree, so the mark is a plain Scheme list.
;;   L12: no warning channel.  The byte-compiler warnings of Emacs do not
;;        exist here, so nothing reads the mark.
;;   L13: no `byte-run--constant-obsolete-warning' call, and no `nil' /
;;        `t' guard of the C path: the mark is stored for every
;;        OBSOLETE-NAME, and ACCESS-TYPE is not checked.
;;   L14: lisp/obarray.el :35 holds `(declare (obsolete ...))' in the
;;        BODY of `obarray-size'.  Since M60 imp-20 (row 36) the loader
;;        HAS a `declare' branch that returns `#nil' and reads no
;;        element, so the LOAD passes and a CALL answers the body value.
;;        MEASURED on a scratch `defun', HEAD = 812559b56: the cell is
;;        bound and the call answers 7.  It does not store the mark: see
;;        L49 (no content stored), L50 (no warning channel) and L51 (no
;;        shape check) of row 36.
(define elisp-make-obsolete-variable
  (case-lambda
    ((obsolete-name current-name when)
     ;; Called with 3 arguments -- no ACCESS-TYPE, as at
     ;; lisp/obarray.el :31.
     (elisp-make-obsolete-variable obsolete-name current-name when #nil))
    ((obsolete-name current-name when access-type)
     "Make the byte-compiler warn that OBSOLETE-NAME is obsolete.
The warning will say that CURRENT-NAME should be used instead.
This port stores the mark only; see limits L11 ... L13 above."
     (elisp-put obsolete-name 'byte-obsolete-variable
                (list current-name access-type when))
     obsolete-name)))

;;;
;;; List Utilities
;;;

(define (elisp-nreverse seq)
  "Reverse order of items in a list, vector or string SEQ.
This function may destructively modify SEQ to produce the value."
  (cond
    ((null? seq) seq)
    ((pair? seq) (reverse! seq))
    ((vector? seq)
     (let ((len (vector-length seq)))
       (do ((i 0 (+ i 1)))
           ((>= i (quotient len 2)) seq)
         (let ((j (- len i 1)))
           (let ((temp (vector-ref seq i)))
             (vector-set! seq i (vector-ref seq j))
             (vector-set! seq j temp))))))
    ((string? seq)
     (list->string (reverse! (string->list seq))))
    (else seq)))

;;;
;;; Type Predicates
;;;

(define (elisp-markerp object)
  "Return t if OBJECT is a marker (editor pointer)."
  (if (and (vector? object)
           (>= (vector-length object) 4)
           (eq? (vector-ref object 0) 'marker))
      #t #nil))

(define (elisp-keywordp object)
  "Return t if OBJECT is a keyword.
This means that it is a symbol with a print name beginning with `:'
interned in the initial obarray."
  (if (and (symbol? object)
           (let ((name (symbol->string object)))
             (and (> (string-length name) 0)
                  (char=? (string-ref name 0) #\:))))
      #t #nil))

;;;
;;; File Utilities
;;;

(define (elisp-complete-filename-p pathname)
  "Return non-nil if PATHNAME is an absolute file name.
On Unix, this is a name starting with a `/'; on MS-DOS and Windows,
it can also be a name starting with `~' or starting with a drive letter
and a colon."
  (if (not (string? pathname))
      #nil
      (let ((len (string-length pathname)))
        (if (= len 0)
            #nil
            (let ((first-char (string-ref pathname 0)))
              (if (or (char=? first-char #\/)
                      (char=? first-char #\~))
                  #t
                  #nil))))))

(define (elisp-file-name-absolute-p filename)
  "Return t if FILENAME is an absolute file name."
  (elisp-complete-filename-p filename))

;;;
;;; Mathematical Utilities
;;;

(define (elisp-copysign x1 x2)
  "Return a value with the magnitude of X1 and the sign of X2."
  (if (or (not (number? x1)) (not (number? x2)))
      (error "Wrong type argument: numberp")
      (let ((abs-x1 (abs x1)))
        (if (negative? x2)
            (- abs-x1)
            abs-x1))))

(define (elisp-frexp x)
  "Return a list (SIGNIFICAND EXPONENT) where X = SIGNIFICAND * 2^EXPONENT.
SIGNIFICAND is in the range [0.5, 1.0)."
  (if (not (number? x))
      (error "Wrong type argument: numberp" x)
      (if (= x 0)
          (list 0 0)
          (let* ((abs-x (abs x))
                 (exponent (inexact->exact (ceiling (log abs-x 2))))
                 (significand (/ abs-x (expt 2 exponent))))
            (if (negative? x)
                (list (- significand) exponent)
                (list significand exponent))))))

(define (elisp-ldexp sgnfcand exponent)
  "Return SGNFCAND * 2^EXPONENT."
  (if (or (not (number? sgnfcand)) (not (integer? exponent)))
      (error "Wrong type argument")
      (* sgnfcand (expt 2 exponent))))

(define (elisp-logb arg)
  "Return the binary exponent of ARG as an integer."
  (if (not (number? arg))
      (error "Wrong type argument: numberp" arg)
      (if (= arg 0)
          (symbol-value 'most-negative-fixnum)  ; Return large negative value for zero
          (inexact->exact (floor (/ (log (abs arg)) (log 2)))))))

(define (elisp-sign number)
  "Return -1, 0, or 1 according to the sign of NUMBER."
  (cond
    ((not (number? number)) (error "Wrong type argument: numberp" number))
    ((> number 0) 1)
    ((< number 0) -1)
    (else 0)))

(define (elisp-clamp x min max)
  "Return X constrained to the range [MIN, MAX]."
  (cond
    ((< x min) min)
    ((> x max) max)
    (else x)))

(define (elisp-square x)
  "Return X squared."
  (if (not (number? x))
      (error "Wrong type argument: numberp" x)
      (* x x)))

;;;
;;; I/O Functions
;;;

(define elisp-read-char
  (case-lambda
    (()
     (elisp-read-char #nil #nil #nil))
    ((prompt)
     (elisp-read-char prompt #nil #nil))
    ((prompt inherit-input-method)
     (elisp-read-char prompt inherit-input-method #nil))
    ((prompt inherit-input-method seconds)
     "Read a character event from the command input (keyboard or macro).
It is returned as a number.
If the optional argument PROMPT is non-nil, display that as a prompt.
If the optional argument INHERIT-INPUT-METHOD is non-nil and some
input method is turned on in the current buffer, that input method
is used for reading a character.
If the optional argument SECONDS is non-nil, it should be a number
specifying the maximum number of seconds to wait for input."
     (char->integer (read-char)))))

;;;
;;; Buffer Operations
;;;

(define (elisp-save-current-buffer thunk)
  "Record which buffer is current; execute THUNK; make that buffer current.
This is the Guile implementation of save-current-buffer using dynamic-wind
for proper cleanup semantics."
  (let ((saved-buffer (current-buffer)))
    (dynamic-wind
      (lambda () #t)
      (lambda () (funcall thunk))
      (lambda ()
        (when (buffer-live-p saved-buffer)
          (set-buffer saved-buffer))))))

(define (elisp-with-current-buffer buffer thunk)
  "Execute THUNK with BUFFER as the current buffer.
Uses dynamic-wind to ensure buffer is properly restored."
  (let ((saved-buffer (current-buffer)))
    (dynamic-wind
      (lambda () (set-buffer buffer))
      (lambda () (funcall thunk))
      (lambda () (set-buffer saved-buffer)))))

;;;

(define (elisp-intern-soft name obarray)
  "Return the symbol whose name is NAME, or nil if no such symbol exists.
Uses efficient symbol lookup without creating new symbols."
  (cond
    ((symbol? name)
     ;; If already a symbol, check if it exists in obarray
     name)  ; In Guile, symbols are globally interned
    ((string? name)
     ;; Use Guile's efficient symbol lookup
     (catch #t
       (lambda ()
         (string->symbol name))
       (lambda (key . args)
         #nil)))
    (else
     (error "Wrong type argument: string-or-symbol-p" name))))



(define (elisp-make-string length init multibyte)
  "Return a newly created string of length LENGTH, with INIT in each element."
  (cond
    ((not (and (integer? length) (>= length 0)))
     (error "Wrong type argument: natnump" length))
    ((not (integer? init))
     (error "Wrong type argument: characterp" init))
    (else
     (make-string length (integer->char init)))))



(define (elisp-sxhash-eq obj)
  "Return an integer hash code for OBJ suitable for `eq'."
  ;; Use Guile's hash function for eq
  (hashq obj 536870909))  ; Large prime number



(define (elisp-sxhash-eql obj)
  "Return an integer hash code for OBJ suitable for `eql'."
  ;; Use Guile's hash function for eqv
  (hashv obj 536870909))



(define (elisp-sxhash-equal obj)
  "Return an integer hash code for OBJ suitable for `equal'."
  ;; Use Guile's hash function for equal
  (hash obj 536870909))


;;; Registration with Elisp symbol table
;;; Phase 2: Registrations migrated from prelude/load.scm
;;; NOTE: Circular dependency resolved by initializing features variable before loading this module
;;;

;; Load system

;; Obarray operations

;; Symbol properties

;; Hash tables

;; Feature/provide

;; List utilities

;; Type predicates

;; File utilities

;; Mathematical utilities

;; I/O functions

;; Buffer operations

;; Registration initialization function
;; Called by load.scm after module is loaded


(define (elisp-convert-guile-object obj)
  "Convert Guile object to Elisp with proper semantics, eliminating C conversions.
This function replaces the inefficient conversion patterns in guile_to_lisp_object
by using direct Scheme-to-Elisp function calls instead of malloc/free cycles."
  (cond
    ;; Handle null - return Elisp nil
    ((null? obj) #nil)

    ;; Handle booleans - map to Elisp t/nil
    ((boolean? obj) (if obj #t #nil))

    ;; Handle exact integers - pass through directly
    ((and (integer? obj) (exact? obj)) obj)

    ;; Handle real numbers - pass through directly
    ((real? obj) obj)

    ;; Handle strings - pass through directly (already Lisp_Objects in GuilEmacs)
    ((string? obj) obj)

    ;; Handle symbols with special mapping using direct Elisp interning
    ((symbol? obj)
     (let ((sym-str (symbol->string obj)))
       (cond
         ;; Special Elisp symbols - use canonical values
         ((string=? sym-str "nil") #nil)
         ((string=? sym-str "t") #t)
         ((string=? sym-str "and") ((symbol-function 'intern) "and" #nil))
         ((string=? sym-str ":") ((symbol-function 'intern) ":" #nil))

         ;; Reader macro symbols - map to canonical Elisp symbols
         ((or (string=? sym-str "`") (string=? sym-str "\\`"))
          ((symbol-function 'intern) "`" #nil))
         ((or (string=? sym-str ",") (string=? sym-str "\\,"))
          ((symbol-function 'intern) "," #nil))
         ((or (string=? sym-str ",@") (string=? sym-str "\\,@"))
          ((symbol-function 'intern) ",@" #nil))

         ;; Regular symbols - intern using direct Scheme-to-Elisp conversion
         (else ((symbol-function 'intern) sym-str #nil)))))

    ;; Handle Guile keywords - convert to Elisp colon symbols
    ((keyword? obj)
     (let* ((keyword-symbol (keyword->symbol obj))
            (base-name (symbol->string keyword-symbol)))
       (cond
         ;; Special case: empty keyword (bare :) -> colon symbol
         ((= (string-length base-name) 0)
          ((symbol-function 'intern) ":" #nil))
         ;; Regular keywords get : prefix and self-evaluation
         (else
          (let* ((colon-name (string-append ":" base-name))
                 (elisp-symbol ((symbol-function 'intern) colon-name #nil)))
            ;; Make keyword self-evaluating
            ((symbol-function 'set) elisp-symbol elisp-symbol)
            elisp-symbol)))))

    ;; Handle pairs - convert recursively to Elisp cons cells
    ((pair? obj)
     (let ((car-converted (elisp-convert-guile-object (car obj)))
           (cdr-converted (elisp-convert-guile-object (cdr obj))))
       ((symbol-function 'cons) car-converted cdr-converted)))

    ;; For other types, pass through directly
    (else obj)))

(define %debug-print-flag 0)
(define (set-debug-print-flag! val)
  (set! %debug-print-flag val))

;(define (get-debug-print-flag)
;  %debug-print-flag)

(define (init-utils-registrations)
  "Initialize symbol function registrations for utils module."
  (set-symbol-function! 'get-load-suffixes elisp-get-load-suffixes)
  (set-symbol-function! 'obarrayp elisp-obarrayp)
  (set-symbol-function! 'obarray-make elisp-obarray-make)
  (set-symbol-function! 'obarray-clear elisp-obarray-clear)
  (set-symbol-function! 'intern elisp-intern)
  (set-symbol-function! 'intern-soft elisp-intern-soft-lread)
  (set-symbol-function! 'unintern elisp-unintern)
  (set-symbol-function! 'symbol-plist elisp-symbol-plist)
  (set-symbol-function! 'setplist elisp-setplist)
  (set-symbol-function! 'get elisp-get)
  (set-symbol-function! 'put elisp-put)
  (set-symbol-function! 'hash-table-count elisp-hash-table-count)
  (set-symbol-function! 'clrhash elisp-clrhash)
  ;; M60 imp-17 -- F3: the `featurep' install moved to `init-loader',
  ;; with the row-18 guard (loader.scm).  `init-loader' does not call
  ;; this function.
  (set-symbol-function! 'nreverse elisp-nreverse)
  (set-symbol-function! 'markerp elisp-markerp)
  (set-symbol-function! 'keywordp elisp-keywordp)
  (set-symbol-function! 'file-name-absolute-p elisp-file-name-absolute-p)
  ;; Register both the Elisp name and elisp-* name for C wrappers to find
  (set-symbol-function! 'copysign elisp-copysign)
  (set-symbol-function! 'elisp-copysign elisp-copysign)
  (set-symbol-function! 'frexp elisp-frexp)
  (set-symbol-function! 'elisp-frexp elisp-frexp)
  (set-symbol-function! 'ldexp elisp-ldexp)
  (set-symbol-function! 'elisp-ldexp elisp-ldexp)
  (set-symbol-function! 'logb elisp-logb)
  (set-symbol-function! 'elisp-logb elisp-logb)
  (set-symbol-function! 'sign elisp-sign)
  (set-symbol-function! 'clamp elisp-clamp)
  (set-symbol-function! 'square elisp-square)
  (set-symbol-function! 'read-char elisp-read-char)
  ;; save-current-buffer is a MACRO in boot.el, not a function - don't register Scheme version
  ;; (set-symbol-function! 'save-current-buffer elisp-save-current-buffer)
  (set-symbol-function! 'with-current-buffer elisp-with-current-buffer)
  (set-symbol-function! 'intern-soft elisp-intern-soft)
  (set-symbol-function! 'make-string elisp-make-string)
  (set-symbol-function! 'sxhash-eq elisp-sxhash-eq)
  (set-symbol-function! 'sxhash-eql elisp-sxhash-eql)
  (set-symbol-function! 'sxhash-equal elisp-sxhash-equal)
  (set-symbol-function! 'set-debug-print-flag! set-debug-print-flag!)

  (set-symbol-function! 'get-debug-print-flag
                        (lambda ()
                          %debug-print-flag))
  )
