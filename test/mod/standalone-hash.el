;;; M60 imp-15 fixture: the row-32 `make-hash-table' family through the
;;; REAL reader and evaluator.  `init-loader' installs the 14 cells
;;; behind the row-18 guard (loader.scm), so this file needs no cell of
;;; its own and every call below goes through the SAME cell that a real
;;; elisp caller uses.  The results are read back by the row-32 cases of
;;; standalone-tests.scm.
;;;
;;; 1 SRFI-69 table IS the elisp object (D1).  `hash-table-p' is the
;;; existing `elisp-hash-table-p' (types.scm :444), and
;;; `hash-table-count' counts ENTRIES: SRFI-69 `hash-table-size' counts
;;; entries (measured: 2 after 2 inserts).
;;;
;;; The 5 RAISE shapes are NOT here.  A raise aborts the whole elisp
;;; load, so mode `hash' of test/m60/probe-imp3.scm owns them, and the
;;; suite calls the cells itself to pin the texts.

;; Hash case 1 -- an `equal' table.  A key that is `equal?' but not `eq?' to
;; the stored key is FOUND, because D2 gives the table the `equal?'
;; equivalence and the `hash' hash function.
(setq standalone-hash-table (make-hash-table :test #'equal))
(setq standalone-hash-put-ret
      (puthash 'standalone-hash-key 42 standalone-hash-table))
(setq standalone-hash-found
      (gethash 'standalone-hash-key standalone-hash-table))
;; An absent key gives the elisp nil, and the DEFAULT when one is given.
(setq standalone-hash-absent
      (gethash 'standalone-hash-nope standalone-hash-table))
(setq standalone-hash-default
      (gethash 'standalone-hash-nope standalone-hash-table
               'standalone-hash-fallback))
(puthash '(1 2) 'standalone-hash-list-value standalone-hash-table)
(setq standalone-hash-equal-hit
      (gethash '(1 2) standalone-hash-table 'standalone-hash-absent))
(setq standalone-hash-put-ret-2
      (puthash 'standalone-hash-key 43 standalone-hash-table))
(setq standalone-hash-count (hash-table-count standalone-hash-table))
;; The predicate: a table is t, a list is the elisp nil.
(setq standalone-hash-p (hash-table-p standalone-hash-table))
(setq standalone-hash-list-p (hash-table-p '(1 2)))

;; Hash case 2 -- an `eq' table does NOT find an `equal?' but not `eq?' copy,
;; and keeps 2 such keys as 2 ENTRIES.
(setq standalone-hash-eq-table (make-hash-table :test #'eq))
(puthash '(1 2) 'standalone-hash-a standalone-hash-eq-table)
(puthash '(1 2) 'standalone-hash-b standalone-hash-eq-table)
(setq standalone-hash-eq-count (hash-table-count standalone-hash-eq-table))
(setq standalone-hash-eq-miss
      (gethash '(1 2) standalone-hash-eq-table 'standalone-hash-absent))

;; Hash case 3 -- the DEFAULT test is `eql' (C :5314): a bare table AND a
;; `:test nil' table both keep 2 `equal?' but not `eq?' keys.
(setq standalone-hash-default-table (make-hash-table))
(puthash '(1 2) 'standalone-hash-a standalone-hash-default-table)
(puthash '(1 2) 'standalone-hash-b standalone-hash-default-table)
(setq standalone-hash-default-count
      (hash-table-count standalone-hash-default-table))
(setq standalone-hash-nil-test-table (make-hash-table :test nil))
(puthash '(1 2) 'standalone-hash-a standalone-hash-nil-test-table)
(puthash '(1 2) 'standalone-hash-b standalone-hash-nil-test-table)
(setq standalone-hash-nil-test-count
      (hash-table-count standalone-hash-nil-test-table))

;; Hash case 4 -- a REPEATED keyword keeps the FIRST value (C :5294 reads the
;; argument vector RIGHT to LEFT).  With `eq' first, the 2 `equal?' keys
;; stay 2 ENTRIES; an `equal' first would give 1.
(setq standalone-hash-repeat-table (make-hash-table :test #'eq :test #'equal))
(puthash '(1 2) 'standalone-hash-a standalone-hash-repeat-table)
(puthash '(1 2) 'standalone-hash-b standalone-hash-repeat-table)
(setq standalone-hash-repeat-count
      (hash-table-count standalone-hash-repeat-table))

;; Hash case 5 -- the accepted keywords.  A valid `:weakness' is PARSED and
;; IGNORED (limit L37), `:purecopy' is IGNORED (D5), and the 2 obsolete
;; rehash keywords are read and ignored (C :5307).
(setq standalone-hash-keywords-table
      (make-hash-table :test #'equal :weakness 'key :purecopy t
                       :size 7 :rehash-size 100 :rehash-threshold 0.5))
(setq standalone-hash-keywords-p
      (hash-table-p standalone-hash-keywords-table))

;; Hash case 6 -- `remhash' returns the elisp nil in BOTH cases, because C
;; `Fremhash' (:5491) calls `hash_remove_from_table' and then returns
;; Qnil with no test for presence.  `clrhash' returns the SAME table and
;; the count is 0 after it.
(setq standalone-hash-remhash-ret
      (remhash 'standalone-hash-key standalone-hash-table))
(setq standalone-hash-count-after-remhash
      (hash-table-count standalone-hash-table))
(setq standalone-hash-remhash-absent
      (remhash 'standalone-hash-nope standalone-hash-table))
(setq standalone-hash-clear-ret (clrhash standalone-hash-table))
(setq standalone-hash-clear-same
      (eq standalone-hash-clear-ret standalone-hash-table))
(setq standalone-hash-count-after-clear
      (hash-table-count standalone-hash-clear-ret))

;; Hash case 7 -- the 7 ACCESSOR cells of row 32 (brief.org P1), through
;; the elisp path.  `hash-table-test' answers the test SYMBOL (D6, read
;; from the SRFI-69 equivalence function), `hash-table-size' answers the
;; ENTRY count (L38), `hash-table-weakness' answers the elisp nil (L37),
;; the 2 obsolete rehash accessors answer the C constants (1.5 and
;; 0.8125), and `hash-table-keys'/`-values' answer the entries.
(setq standalone-hash-accessor-table (make-hash-table :test #'equal))
(puthash 'standalone-hash-ak 7 standalone-hash-accessor-table)
(setq standalone-hash-accessor-test
      (hash-table-test standalone-hash-accessor-table))
(setq standalone-hash-accessor-size
      (hash-table-size standalone-hash-accessor-table))
(setq standalone-hash-accessor-weakness
      (hash-table-weakness standalone-hash-accessor-table))
(setq standalone-hash-accessor-rehash-size
      (hash-table-rehash-size standalone-hash-accessor-table))
(setq standalone-hash-accessor-rehash-threshold
      (hash-table-rehash-threshold standalone-hash-accessor-table))
(setq standalone-hash-accessor-keys
      (hash-table-keys standalone-hash-accessor-table))
(setq standalone-hash-accessor-values
      (hash-table-values standalone-hash-accessor-table))
