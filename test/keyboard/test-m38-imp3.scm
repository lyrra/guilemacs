;;; test-m38-imp3.scm --- M38 imp-3: isolate the input-state leak (D3).
;;;
;;; brief.org (M38 imp-3, defect D3).  The keyboard corpora run in ONE
;;; emacs process (tool/run-tests.scm:12), so a name one corpus writes
;;; stays written for every corpus that follows.  This corpus holds the
;;; SOURCE checks of the fix:
;;;
;;;   1. the repo root is bound by the wrapper (%m38-root);
;;;   2. every writer corpus of §5.1 loads the one shared reset helper
;;;      (test/keyboard/test-m38-imp3-reset.el) AND calls it inside
;;;      unwind-protect (normal + non-local exit path, §8.1);
;;;   3. the helper's name list is the §5.4 default list (drift guard);
;;;   4. no other corpus calls the reset — the §5.1 writer list is
;;;      complete, and no writer was added without updating the list;
;;;   5. the two no-reset victims use Pattern B (§8.3): the recent-keys
;;;      ring measures a delta, the mouse_moved check measures the
;;;      corpus's own effect;
;;;   6. the kbd-wait-loop corpus drains kbd_buffer[] (§8.4 item 6);
;;;   8. no victim expectation changed;
;;;   9. no C file changed — the C surface stays 11,711 lines;
;;;  10. the two --filter=keyboard runs exit 0 and give the same, empty
;;;      FAIL set (exit criterion 3).  This check reads the two log
;;;      files the .el wrapper wrote; the wrapper binds their paths and
;;;      the two exit statuses.  Under the recursion guard the wrapper
;;;      binds nothing and the check is an INFO line;
;;;  11. the wrapper bounds each nested run with `timeout' (review F5).
;;;
;;; (Item 7 used to check that test-m37-imp3.scm's docs/ dependency kept
;;; its `tracks-milestone?' skip guard (the m35-imp3 disposition, §7):
;;; milestone.org is a live tracker whose content rotates away from an
;;; old milestone, so a check that reads it unconditionally could
;;; false-fail once M37 was no longer the current milestone.  A later,
;;; separate cleanup removed docs/kb.org- and milestone.org-dependent
;;; checks from test-m37-imp3.scm (and six sibling corpora) entirely --
;;; docs/ is gitignored and not kept in sync with the git-tracked
;;; test/code work, so those checks were either always-skip or failed on
;;; stale local docs unrelated to code correctness.  That removal is a
;;; strictly stronger fix for the same doc-anchor-failure problem class
;;; item 7 covered (no docs/ read at all, so nothing to skip or
;;; false-fail), which makes the `tracks-milestone?' guard item 7 pinned
;;; moot.  Item 7 is removed rather than re-pointed at a guard that no
;;; longer exists.)
;;;
;;; Residual risk (§5.1 NOTE, review F3).  brief.org §5.1 records that
;;; "Virtual core pointer" and "Virtual core keyboard" are real X device
;;; names, so a real event picked up by a corpus can write
;;; last-event-device from PRODUCTION code, not from a corpus.  The
;;; reset covers only the 2 kbd writers, and an X event during any other
;;; corpus is not covered.  §8.1 directs: record the finding and name a
;;; follow-up.  Disposition: follow-up in M38 imp-4 (close-out); see
;;; docs/m38-plan.org §D3.  The value is harmless in production (a real
;;; device name), so the test side is not patched further.
;;;
;;; Batch-safe: it reads files.  The repo root is bound as %m38-root.

(use-modules (ice-9 rdelim))
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

;; fail-set: the corpus FAIL lines and the harness ERROR lines of a
;; harness log, sorted.  brief.org §5.2 prints a test failure as
;; "FAIL <name> [...]"; ERT prints "FAILED n/m ...", which the trailing
;; space excludes.  The harness also reports an ERT count mismatch as
;; "ERROR: ..." (review F8); a run that fails only by a count mismatch
;; has no FAIL line, so the ERROR prefix is required for a full failure
;; test.  The exit-status check covers that case too.
(define (fail-set path)
  (let ((lines (split-lines* (slurp path))))
    (sort (filter (lambda (l) (or (string-prefix? "FAIL " l)
                                  (string-prefix? "ERROR:" l)))
                  lines)
          string<?)))

;;; --- 1. The repo root must be known --------------------------------
(if (not (defined? '%m38-root))
    (begin (report "m38/imp3/root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m38-root "."))
    (report "m38/imp3/root-bound" 'PASS))

;;; The writer map of brief.org §5.1.
(define m38-imp3-writers
  '("test/keyboard/test-m13-store.el"
    "test/keyboard/test-m20-menu-prompt.el"
    "test/keyboard/test-m21-read-key-sequence.el"
    "test/keyboard/test-m22-imp3.el"
    "test/keyboard/test-m22-imp4.el"
    "test/keyboard/test-kbd-dispatch.el"
    "test/keyboard/test-kbd-wait-loop.el"))

;;; --- 2. Each writer loads the helper and clears inside unwind-protect
;;; A bare call is not enough: the clear must run on the non-local exit
;;; path too (§8.1), so the file must also contain unwind-protect.  Match
;;; the EXACT call form (review F7): a writer that stops calling the
;;; helper but keeps the words in a comment must fail this check.
(define m38-imp3-call-form "(m38-imp3-reset-input-state m38-imp3-entry-buffer)")
(define (writer-clears? file)
  (let ((b (slurp (repo file))))
    (and b
         (has? b "test-m38-imp3-reset.el")
         (has? b m38-imp3-call-form)
         (has? b "unwind-protect"))))

(for-each
 (lambda (f)
   (check (string-append "m38/imp3/writer-clears/" f) #t (writer-clears? f)))
 m38-imp3-writers)

;;; --- 2b. A reset error reaches the fail-set (review §3.4) ----------
;;; The writer cleanup prints the reset error with the "ERROR:" prefix,
;;; so both the harness fail-set and the two-run check (§10) see it.  A
;;; bare "M38-IMP3-RESET-ERROR:" line matches neither the FAIL prefix
;;; nor the ERROR prefix, so a failing reset could pass the gate.
(for-each
 (lambda (f)
   (check (string-append "m38/imp3/writer-reset-error/" f) #t
          (has? (slurp (repo f)) "ERROR: M38-IMP3-RESET-ERROR")))
 m38-imp3-writers)

;;; --- 3. The helper's name list is the §5.4 list --------------------
;;; The helper is the single source of truth (§8.2).  Check every default
;;; name appears in it, and that it sets deactivate-mark in the buffer
;;; the corpus started in (§8.4 item 4).
(define m38-imp3-helper (slurp (repo "test/keyboard/test-m38-imp3-reset.el")))
(for-each
 (lambda (n)
   (check (string-append "m38/imp3/helper-clears/" n) #t (has? m38-imp3-helper n)))
 '("last-input-event" "last-nonmenu-event" "last-event-frame"
   "deactivate-mark" "last-event-device" "num-nonmacro-input-events"))
(check "m38/imp3/helper/runs-from-eval-scheme" #t
       (has? m38-imp3-helper "eval-scheme"))
;; F2: the helper must make the entry buffer current (set-buffer), NOT
;; wrap the clear in with-current-buffer (which restores the leaked
;; buffer on exit and leaves it current).  Match the exact (set-buffer b)
;; call, not the docstring word.
(check "m38/imp3/helper/restores-entry-buffer" #t
       (has? m38-imp3-helper "(set-buffer b)"))
(check "m38/imp3/helper/no-with-current-buffer" #f
       (has? m38-imp3-helper "(with-current-buffer"))

;;; --- 4. No other writer; the §5.1 list is complete -----------------
;;; Scan the keyboard .el corpora for a reset CALL SITE.  The helper's
;;; own (defun ...) does not match the call prefix.  The set of callers
;;; must equal the §5.1 writer list.  Exclude the helper file by NAME
;;; (review F6): a later docstring or comment that writes the call form
;;; would otherwise add the helper to the caller set.
(define (reset-caller? name)
  (and (string-suffix? ".el" name)
       (not (string=? name "test-m38-imp3-reset.el"))
       (has? (slurp (string-append %m38-root "/test/keyboard/" name))
             m38-imp3-call-form)))

(define m38-imp3-callers
  (sort (filter reset-caller?
                (scandir (string-append %m38-root "/test/keyboard")))
        string<?))
(define m38-imp3-expected-callers
  (sort (map (lambda (p) (substring p (+ 1 (string-rindex p #\/))))
             m38-imp3-writers)
        string<?))
(check "m38/imp3/writers-complete" m38-imp3-expected-callers m38-imp3-callers)

;;; --- 5. Pattern B for the two no-reset victims ---------------------
(define m38-imp3-m22 (slurp (repo "test/keyboard/test-m22-imp3.scm")))
(check "m38/imp3/patternb/recent-keys-delta-pre" #t
       (has? m38-imp3-m22 "m22-imp3-ring-before"))
(check "m38/imp3/patternb/recent-keys-delta-post" #t
       (has? m38-imp3-m22 "m22-imp3-ring-before ((%c 'length) ((%c 'recent-keys))))"))
(check "m38/imp3/patternb/mouse-moved-own-effect" #t
       (has? m38-imp3-m22 "m22-imp3-first-moved-frame"))

;;; --- 6. kbd-wait-loop drains kbd_buffer[] --------------------------
(define m38-imp3-kbdwl (slurp (repo "test/keyboard/test-kbd-wait-loop.scm")))
(check "m38/imp3/drain/kbd-buffer" #t
       (has? m38-imp3-kbdwl "--kbd-set-fetch-ptr-index"))

;;; --- 8. No victim expectation changed ------------------------------
;;; The victims of §5.3 keep their checks.  Grep for the exact default
;;; lines / check names.
(define m38-imp3-victim-cases
  '(("test/keyboard/test-m23-imp2.el"  "(last-input-event nil)")
    ("test/keyboard/test-m23-imp2.el"  "(last-nonmenu-event nil)")
    ("test/keyboard/test-m23-imp2.el"  "(num-nonmacro-input-events 0)")
    ("test/keyboard/test-m23-imp2.el"  "(deactivate-mark nil)")
    ("test/keyboard/test-m23-imp5.el"  "(last-event-frame nil)")
    ("test/keyboard/test-m31-imp1.scm" "m31/imp1/default/")
    ("test/keyboard/test-m22-imp3.scm" "m22/imp3/some-mouse-moved/track-off")
    ("test/keyboard/test-m22-imp3.scm" "m22/imp3/recent-keys-ring-empty-after")
    ("test/keyboard/test-kbd-wait-loop.scm" "end-time-expiry/slot-set")
    ("test/keyboard/test-kbd-wait-loop.scm" "end-time-expiry/entry-sync")))
(for-each
 (lambda (c)
   (let ((file (car c)) (needle (cadr c)))
     (check (string-append "m38/imp3/victim/" needle) #t
            (has? (slurp (repo file)) needle))))
 m38-imp3-victim-cases)

;;; --- 9. No C file changed ------------------------------------------
(check "m38/imp3/c-surface/keyboard.c" 11221
       (line-count (repo "src/keyboard.c")))
(check "m38/imp3/c-surface/keyboard-globals.c" 490
       (line-count (repo "src/keyboard-globals.c")))

;;; --- 10. The two-run proof (exit criterion 3) ----------------------
(if (not (defined? '%m38-imp3-run1))
    (info "m38/imp3/two-run/skipped"
          "nested run (M38-IMP3 recursion guard)")
    (begin
      (check "m38/imp3/two-run/run1-exit" 0 %m38-imp3-exit1)
      (check "m38/imp3/two-run/run2-exit" 0 %m38-imp3-exit2)
      (check "m38/imp3/two-run/run1-fail-empty" '()
             (fail-set %m38-imp3-run1))
      (check "m38/imp3/two-run/run2-fail-empty" '()
             (fail-set %m38-imp3-run2))
      (check "m38/imp3/two-run/fail-sets-agree"
             (fail-set %m38-imp3-run1) (fail-set %m38-imp3-run2))))

(reverse test-results)
