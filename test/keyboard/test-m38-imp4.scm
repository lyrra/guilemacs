;;; test-m38-imp4.scm --- M38 imp-4: close out the test-harness integrity step.
;;;
;;; brief.org (M38 imp-4, §8).  M38 is the test-harness integrity step.
;;; It ports no C code and changes no input asset, so the surface must
;;; NOT move.  imp-4 re-measures the surface, re-confirms the keyboard
;;; gate (exit criterion 3), and records the accounting in the working
;;; documents.  This corpus holds the SOURCE checks of the close-out:
;;;
;;;   1. the repo root is bound by the wrapper (%m38-root);
;;;   2. the surface table of brief.org §6 — every value equals the
;;;      expected value (no C file changed);
;;;   3. the docs/kb.org ** M38 section status is done;
;;;   4. the docs/milestone-overview.org §M38 headline says CLOSED;
;;;   5. the milestone.org §M38 section says CLOSED and the imp-4 record
;;;      is present.  The doc checks are section-scoped (review §3.2) and
;;;      skip with an INFO line when the untracked file is absent
;;;      (review §3.3), like the M36/M37 close-out pins;
;;;   6. the two --filter=keyboard runs exit 0 and give the same, empty
;;;      FAIL set (exit criterion 3).  This check reads the two log files
;;;      the .el wrapper wrote; under the recursion guard the wrapper
;;;      binds nothing and the check is an INFO line.
;;;
;;; Batch-safe: it reads files.  The repo root is bound as %m38-root.

(use-modules (ice-9 rdelim))
(use-modules (ice-9 ftw))
(use-modules (srfi srfi-13))
(use-modules (srfi srfi-1))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (info name value)
  (report name (list 'INFO value)))

(define (slurp path)
  (if (not (file-exists? path))
      #f
      (call-with-input-file path
        (lambda (port)
          (let loop ((chars '()))
            (let ((c (read-char port)))
              (if (eof-object? c)
                  (list->string (reverse chars))
                  (loop (cons c chars)))))))))

(define (has? s sub)
  (and s (string-contains s sub) #t))

(define (repo path) (string-append %m38-root "/" path))

;; count-substr: the number of non-overlapping occurrences of SUB in
;; TEXT, i.e. `grep -o SUB | wc -l`.
(define (count-substr text sub)
  (if (not (string? text)) 0
      (let ((n (string-length sub)))
        (let loop ((i 0) (acc 0))
          (if (> (+ i n) (string-length text))
              acc
              (if (string=? sub (substring text i (+ i n)))
                  (loop (+ i n) (1+ acc))
                  (loop (1+ i) acc)))))))

;; line-count: the number of #\newline in PATH, i.e. `wc -l`.
(define (line-count path)
  (let ((s (slurp path)))
    (and s (let loop ((i 0) (n 0))
             (if (>= i (string-length s))
                 n
                 (loop (+ i 1)
                       (if (char=? (string-ref s i) #\newline) (+ n 1) n)))))))

(define (split-lines* text)
  (if (not text)
      '()
      (let loop ((start 0) (out '()))
        (let ((nl (string-index text #\newline start)))
          (if (not nl)
              (reverse (if (< start (string-length text))
                           (cons (substring text start (string-length text)) out)
                           out))
              (loop (+ nl 1) (cons (substring text start nl) out)))))))

;; count-prefix-lines: the number of lines of PATH that START with
;; PREFIX, i.e. `grep -c '^PREFIX'`.
(define (count-prefix-lines path prefix)
  (let ((lines (split-lines* (slurp path))))
    (length (filter (lambda (l) (string-prefix? prefix l)) lines))))

;; stars: the number of leading #\* in LINE (an org headline depth).
(define (stars line)
  (let loop ((i 0))
    (if (and (< i (string-length line)) (char=? (string-ref line i) #\*))
        (loop (1+ i)) i)))

(define (heading-line? line)
  (let ((n (stars line)))
    (and (> n 0)
         (< n (string-length line))
         (char=? (string-ref line n) #\space))))

;; org-section: the org-mode section of TEXT introduced by the heading
;; line that starts with HEADING, up to the next heading at the same or
;; a shallower level.  #f when the heading is absent.  Used to scope the
;; doc checks to the M38 entry, not the whole file (review §3.2).
(define (org-section text heading)
  (and (string? text)
       (let* ((ls (split-lines* text))
              (level (stars heading))
              (start (list-index (lambda (l) (string-prefix? heading l)) ls)))
         (and start
              (let loop ((i (1+ start)))
                (cond
                 ((>= i (length ls))
                  (string-concatenate
                   (map (lambda (l) (string-append l "\n"))
                        (list-head (list-tail ls start) (- i start)))))
                 ((and (heading-line? (list-ref ls i))
                       (<= (stars (list-ref ls i)) level))
                  (string-concatenate
                   (map (lambda (l) (string-append l "\n"))
                        (list-head (list-tail ls start) (- i start)))))
                 (else (loop (1+ i)))))))))

;; fail-set: the corpus FAIL lines and the harness ERROR lines of a
;; harness log, sorted.  brief.org §5.2 prints a test failure as
;; "FAIL <name> [...]"; ERT prints "FAILED n/m ...", which the trailing
;; space excludes.  The harness also reports an ERT count mismatch as
;; "ERROR: ...".  A green run has an empty fail-set.
(define (fail-set path)
  (let ((lines (split-lines* (slurp path))))
    (sort (filter (lambda (l) (or (string-prefix? "FAIL " l)
                                  (string-prefix? "ERROR:" l)))
                  lines)
          string<?)))

;; src-c-h: the C and header files directly under src/, i.e. the
;; `src/*.c src/*.h` set the scm_c_public_ref count scans.
(define (src-c-h)
  (map (lambda (n) (string-append %m38-root "/src/" n))
       (filter (lambda (n)
                 (or (string-suffix? ".c" n) (string-suffix? ".h" n)))
               (scandir (string-append %m38-root "/src")))))

;;; --- 1. The repo root must be known --------------------------------
(if (not (defined? '%m38-root))
    (begin (report "m38/imp4/root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m38-root "."))
    (report "m38/imp4/root-bound" 'PASS))

;;; --- 2. The surface table (brief.org §6) ---------------------------
;;; M38 changes no C file, so every value equals the expected value.  A
;;; drift here means a C file moved and M38 is not the close-out it
;;; claims to be.
(define m38-imp4-kbd-lines (line-count (repo "src/keyboard.c")))
(define m38-imp4-globals-lines (line-count (repo "src/keyboard-globals.c")))
(check "m38/imp4/surface/keyboard.c" 11221 m38-imp4-kbd-lines)
(check "m38/imp4/surface/keyboard-globals.c" 490 m38-imp4-globals-lines)
(check "m38/imp4/surface/combined" 11711
       (+ (if m38-imp4-kbd-lines m38-imp4-kbd-lines 0)
          (if m38-imp4-globals-lines m38-imp4-globals-lines 0)))
(check "m38/imp4/surface/defuns" 446
       (count-prefix-lines (repo "src/keyboard.c") "DEFUN (\""))
(check "m38/imp4/surface/shims" 420
       (count-prefix-lines (repo "src/keyboard.c") "DEFUN (\"--"))
(check "m38/imp4/surface/public-ref-sites" 159
       (apply + (map (lambda (p) (count-substr (slurp p) "scm_c_public_ref"))
                     (src-c-h))))

;;; --- 3. docs/kb.org ** M38 section is done -------------------------
;;; docs/ is untracked, so a fresh clone has no kb.org: skip with an
;;; INFO line, do not fail (review §3.3).  Scope the checks to the
;;; ** M38 section (review §3.2): a file-wide "status :: done" match
;;; would pass even if the M38 entry lost its own status line.
(define m38-imp4-kb (slurp (repo "docs/kb.org")))
(if (not m38-imp4-kb)
    (info "m38/imp4/doc/kb.org/skipped" "docs/kb.org absent (untracked)")
    (let ((kb-m38 (org-section m38-imp4-kb "** M38")))
      (if (not kb-m38)
          (report "m38/imp4/doc/kb-m38-heading"
                  (cons 'FAIL "no ** M38 section in docs/kb.org"))
          (begin
            (check "m38/imp4/doc/kb-m38-heading" #t (has? kb-m38 "** M38"))
            (check "m38/imp4/doc/kb-m38-closed" #t
                   (has? kb-m38 "isolated — CLOSED (imp-4 close-out)"))
            (check "m38/imp4/doc/kb-status-done" #t (has? kb-m38 "status :: done"))))))

;;; --- 4. docs/milestone-overview.org §M38 says CLOSED ----------------
(define m38-imp4-overview (slurp (repo "docs/milestone-overview.org")))
(if (not m38-imp4-overview)
    (info "m38/imp4/doc/overview/skipped"
          "docs/milestone-overview.org absent (untracked)")
    (let ((ov-m38 (org-section m38-imp4-overview "*** M38")))
      (if (not ov-m38)
          (report "m38/imp4/doc/overview-m38-closed"
                  (cons 'FAIL "no *** M38 section in the overview"))
          (check "m38/imp4/doc/overview-m38-closed" #t
                 (has? ov-m38
                       "test-harness integrity and the two M37 open items (CLOSED)")))))

;;; --- 5. milestone.org §M38 says CLOSED, imp-4 recorded --------------
(define m38-imp4-milestone (slurp (repo "milestone.org")))
(if (not m38-imp4-milestone)
    (info "m38/imp4/doc/milestone/skipped" "milestone.org absent (untracked)")
    (let ((ms-m38 (org-section m38-imp4-milestone "* M38")))
      (if (not ms-m38)
          (report "m38/imp4/doc/milestone-m38-closed"
                  (cons 'FAIL "no * M38 section in milestone.org"))
          (begin
            (check "m38/imp4/doc/milestone-m38-closed" #t
                   (has? ms-m38
                         "test-harness integrity and the two M37 open items (CLOSED)"))
            (check "m38/imp4/doc/milestone-imp4-record" #t
                   (and (has? ms-m38 "imp-4") (has? ms-m38 "Close-out")))))))

;;; --- 6. The two-run proof (exit criterion 3) -----------------------
(if (not (defined? '%m38-imp4-run1))
    (info "m38/imp4/two-run/skipped"
          "nested run (M38-IMP4 recursion guard)")
    (begin
      (check "m38/imp4/two-run/run1-exit" 0 %m38-imp4-exit1)
      (check "m38/imp4/two-run/run2-exit" 0 %m38-imp4-exit2)
      (check "m38/imp4/two-run/run1-fail-empty" '()
             (fail-set %m38-imp4-run1))
      (check "m38/imp4/two-run/run2-fail-empty" '()
             (fail-set %m38-imp4-run2))
      (check "m38/imp4/two-run/fail-sets-agree"
             (fail-set %m38-imp4-run1) (fail-set %m38-imp4-run2))))

;;; --- 7. The doc checks are robust (review §3.2, §3.3) --------------
;;; Pin the shape of THIS file so the two doc-check fixes cannot
;;; regress to the weaker forms the review found.
;;;
;;; §3.2: org-section must limit a section to its own headline.  A
;;; check on the whole file would match a "status :: done" line from
;;; any other milestone.
(define m38-imp4-demo
  "** M38\n  status :: done\n** M39\n  status :: pending\n")
(check "m38/imp4/org-section/in-section" #t
       (has? (org-section m38-imp4-demo "** M38") "status :: done"))
(check "m38/imp4/org-section/out-of-section" #f
       (has? (org-section m38-imp4-demo "** M38") "status :: pending"))
;; §3.3: each untracked doc is guarded, so an absent file prints an
;; INFO line and is not a FAIL.  The guard is "if (not <doc>)".
(define m38-imp4-self (slurp (repo "test/keyboard/test-m38-imp4.scm")))
(check "m38/imp4/shape/kb-absent-guarded" #t
       (and (has? m38-imp4-self "(if (not m38-imp4-kb)")
            (has? m38-imp4-self "docs/kb.org absent (untracked)")))
(check "m38/imp4/shape/overview-absent-guarded" #t
       (and (has? m38-imp4-self "(if (not m38-imp4-overview)")
            (has? m38-imp4-self "docs/milestone-overview.org absent (untracked)")))
(check "m38/imp4/shape/milestone-absent-guarded" #t
       (and (has? m38-imp4-self "(if (not m38-imp4-milestone)")
            (has? m38-imp4-self "milestone.org absent (untracked)")))

(reverse test-results)
