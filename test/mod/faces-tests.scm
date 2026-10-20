;;; SRFI-64 tests for the 2 pure procedures in (emacs faces).

;; COVER: face-attribute-relative-verdict and bitmap-spec-verdict of
;; mod/emacs/faces.scm.  The module imports nothing, so plain
;; `guile -L mod` loads it with no Emacs.

;; LIMIT: read this before you trust a green run.
;;   1. This suite proves the 2 PURE procedures only.
;;   2. It starts no Emacs, starts no subprocess, and runs no C build.
;;   3. It proves NO C seam and NO mod/emacs change on the real path.
;;      The (m59) corpus keeps that proof (test/m59/).
;;   4. A rename of an export breaks this suite.  A broken C dispatcher
;;      leaves it green.
;;   5. The SBYTES byte count is not proved here.  The byte count crosses
;;      the layer as an integer, because a Scheme (string-length ...)
;;      counts characters, not bytes.

;; THE -1 SENTINEL: the C read SYNTHESIZES -1 for a field of the wrong
;; type (src/xfaces.c :856 the -1 initializer, :885 ... :890 the type
;; tests).  A row that holds -1 proves the C-read CONTRACT, not a real
;; Lisp value.  No real value reaches the procedure on those rows.
;;
;; THE data-bytes RULE: the C read passes SBYTES.  (string 1 0) is a
;; TWO-character Elisp string, so its data-bytes is 2.  Plain Guile can
;; not build (string 1 0), so this suite passes the integer 2.  That is
;; why the (8 2) and (9 1) exact-fit rows carry data-bytes 2.
;;
;; THE bytes_per_row RULE: needed = height * (quotient (+ width 7) 8).
;; Imp-4 deleted that rule from C, so the 3 too-short controls of table C
;; keep it covered, each with its exact-fit partner.  (8 2) at data-bytes
;; 2 is an EXACT FIT and not a control; the control is (8 3).

(use-modules (srfi srfi-64)
             (emacs faces))

;; Pinned case count.  A suite that loses a case must fail: each suite
;; pins its own count (docs/kb.org test-mod-standalone-suite).
(define expected-passes 28)

;; No SRFI-64 log file: it would land in the working directory.  See
;; the same note, docs/kb.org test-mod-standalone-suite.
(set! test-log-to-file #f)

(test-begin "Guilemacs faces module")
(define test-runner (test-runner-current))

;; Table A: the 8-row truth table of face-attribute-relative-verdict,
;; 3 booleans in (same-as-unspecified? height? fixnum?), 1 boolean out.
;; Rows A1 ... A4 expand the single folded row "a true wins before the
;; :height test", so a rewrite can not hide behind a folded row.
;; A7 and A8 make branch 3 explicit for both values of fixnum?.
;; plain guile 3.0.10, HEAD 3622bded2.
(test-equal "A1 (#t #t #t) a wins before the :height test"
            #t (face-attribute-relative-verdict #t #t #t))
(test-equal "A2 (#t #t #f) a wins before the :height test"
            #t (face-attribute-relative-verdict #t #t #f))
(test-equal "A3 (#t #f #t) a wins before the :height test"
            #t (face-attribute-relative-verdict #t #f #t))
(test-equal "A4 (#t #f #f) a wins before the :height test"
            #t (face-attribute-relative-verdict #t #f #f))
(test-equal "A5 (#f #t #t) a fixnum height is absolute"
            #f (face-attribute-relative-verdict #f #t #t))
(test-equal "A6 (#f #t #f) a float height is relative"
            #t (face-attribute-relative-verdict #f #t #f))
(test-equal "A7 (#f #f #t) branch 3, no :height"
            #f (face-attribute-relative-verdict #f #f #t))
(test-equal "A8 (#f #f #f) branch 3, no :height"
            #f (face-attribute-relative-verdict #f #f #f))

;; Table B: 14 rows of bitmap-spec-verdict, 4 plain values in
;; (file-name? width height data-bytes), 1 boolean out.  Every row is a
;; distinct input tuple.  Each row comment gives the Elisp witness, which
;; plain Guile can not build (no (string 2 0), no (string 1 0)).
(test-equal "B1 (#t -1 -1 -1) a file name wins, the 3 numbers are unused"
            #t (bitmap-spec-verdict #t -1 -1 -1))   ; (bitmap-spec-p "x")
(test-equal "B2 (#f 8 1 1) exact fit, 1 byte per row"
            #t (bitmap-spec-verdict #f 8 1 1))      ; (list 8 1 "A") SBYTES 1
(test-equal "B3 (#f 8 2 2) EXACT FIT at 2 bytes"
            #t (bitmap-spec-verdict #f 8 2 2))      ; (list 8 2 (string 2 0))
(test-equal "B4 (#f 9 1 2) EXACT FIT, 2 row bytes"
            #t (bitmap-spec-verdict #f 9 1 2))      ; (list 9 1 (string 1 0))
(test-equal "B5 (#f 8 2 4) extra DATA is accepted"
            #t (bitmap-spec-verdict #f 8 2 4))      ; (list 8 2 "A\0\0\0")
(test-equal "B6 (#f 8 2 -1) DATA is absent, C-read contract -1"
            #f (bitmap-spec-verdict #f 8 2 -1))     ; (list 8 2)
(test-equal "B7 (#f 0 1 2) WIDTH is below 1"
            #f (bitmap-spec-verdict #f 0 1 2))      ; (list 0 1 (string 2 0))
(test-equal "B8 (#f 8 0 1) HEIGHT is below 1"
            #f (bitmap-spec-verdict #f 8 0 1))      ; (list 8 0 "A")
(test-equal "B9 (#f -1 2 2) WIDTH is not a fixnum, C-read contract -1"
            #f (bitmap-spec-verdict #f -1 2 2))     ; (list 8.0 2 (string 2 0))
;; B10 covers 2 sources with one tuple: DATA = 42 and DATA = nil.  Both
;; are not a string, both cross as the same -1 tuple, so pin it once.
(test-equal "B10 (#f -1 -1 -1) DATA is 42 or nil, C-read contract -1"
            #f (bitmap-spec-verdict #f -1 -1 -1))   ; 42 and nil
;; B11 is #f for 2 reasons at once: the width bound AND the DATA coverage
;; of 1 byte.  So it can not observe the bound alone; B12 and B13 do.
(test-equal "B11 (#f 2147483648 1 1) INT_MAX + 1, and DATA is short too"
            #f (bitmap-spec-verdict #f 2147483648 1 1))
;; B12 and B13 are ONE pair and the only observable of the width bound
;; alone, because 268435456 = (2147483647 + 7) / 8.  They need a DATA
;; string of 268435456 bytes (256 MiB), so no real-path row carries them.
(test-equal "B12 (#f 2147483647 1 268435456) the width bound holds"
            #t (bitmap-spec-verdict #f 2147483647 1 268435456))
(test-equal "B13 (#f 2147483648 1 268435456) the width bound breaks"
            #f (bitmap-spec-verdict #f 2147483648 1 268435456))
;; B14 is the only observable of the height bound.  MEASURED: with the
;; height clause deleted the row gives #t.  It needs a DATA string of
;; 2147483648 bytes (2 GiB), so no real-path row carries it.
(test-equal "B14 (#f 1 2147483648 2147483648) the height bound breaks"
            #f (bitmap-spec-verdict #f 1 2147483648 2147483648))

;; The (>= data-bytes 0) clause has NO observable, so it takes no row:
;; MEASURED, with that clause deleted B6 and B10 stay #f, because a
;; negative data-bytes gives a negative quotient.

;; Table C: the 3 too-short controls (8 3), (9 2), (1 8) with their
;; exact-fit partners, so the bytes_per_row rule that imp-4 deleted from C
;; stays covered on both sides of the boundary.  The 6 rows exist for that
;; deleted rule.  Each pair differs only in data-bytes.  Table B already
;; holds the exact fits (8 2) and (9 1).  Table C does not repeat them.
;; All 6 rows are reachable on the real path: (string 1 0) gives 2 bytes,
;; so a longer literal gives the partner.
(test-equal "C1 (#f 8 3 2) too short, 2 bytes cover 2 rows not 3"
            #f (bitmap-spec-verdict #f 8 3 2))
(test-equal "C2 (#f 8 3 3) the exact-fit partner of C1"
            #t (bitmap-spec-verdict #f 8 3 3))
(test-equal "C3 (#f 9 2 2) too short, 2 rows need 4 bytes"
            #f (bitmap-spec-verdict #f 9 2 2))
(test-equal "C4 (#f 9 2 4) the exact-fit partner of C3"
            #t (bitmap-spec-verdict #f 9 2 4))
(test-equal "C5 (#f 1 8 1) too short, 8 rows need 8 bytes"
            #f (bitmap-spec-verdict #f 1 8 1))
(test-equal "C6 (#f 1 8 8) the exact-fit partner of C5"
            #t (bitmap-spec-verdict #f 1 8 8))

(test-end "Guilemacs faces module")

(let ((passes (test-runner-pass-count test-runner))
      (fails  (test-runner-fail-count test-runner)))
  (format #t "~a: ~a passed, ~a failed (expected ~a passed)~%"
          "Guilemacs faces module" passes fails expected-passes)
  (exit (if (and (zero? fails) (= passes expected-passes)) 0 1)))
