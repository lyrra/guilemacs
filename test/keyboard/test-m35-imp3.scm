;;; test-m35-imp3.scm --- M35 imp-3: the close-out audit corpus.
;;;
;;; brief.org (M35 imp-3) is the close-out.  It re-measures the combined
;;; C surface, runs the gate set, records the final remnant, and marks
;;; M35 closed.  imp-3 changes no C file and retires no stub.  This
;;; corpus pins the close-out so the claims are checked automatically
;;; and not only by hand.
;;;
;;; Seven checks (brief.org §5.2):
;;;
;;;   1. The anchored counts.  Read src/keyboard.c and
;;;      src/keyboard-globals.c with the brief.org §3 method.  Assert
;;;      each value equals the value recorded in docs/kb.org ** M35 and
;;;      milestone.org §M35.
;;;   2. The budget.  Assert combined <= 11,960.  Print the margin as
;;;      INFO.
;;;   3. The three M34 retirements stay gone: safe_run_hooks_2,
;;;      push_kboard, and not_single_kboard_state have no definition, no
;;;      extern, and no live caller.  A comment mention alone is not a
;;;      caller.  A whole-identifier scan is used, so the xdisp.c
;;;      dispatcher xdisp_push_kboard does not count as push_kboard.
;;;   4. The nine residual stubs keep a live buildable C caller.  One
;;;      check per stub.  An NS file (nsterm.m, nsmenu.m) is not a live
;;;      caller, because HAVE_NS is undefined (src/config.h).
;;;   5. The kbd_buffer_store_event census.  Assert 15 caller files (14
;;;      buildable + 1 NS = nsterm.m).  This is the imp-0 correction to
;;;      the earlier "16".
;;;   6. The accounting rows exist.  Assert that docs/kb.org ** M35 holds
;;;      status :: closed, that docs/milestone-overview.org §M35 says
;;;      CLOSED, and that milestone.org marks imp-3 done.
;;;   7. The guard test of imp-1 stays correct.  Keep the two comment
;;;      anchors current: src/xdisp.c:582 and src/keyboard.c:3927.
;;;
;;; Each check reads the name and the value that it pins.  A single
;;; prose phrase is not enough.  A dropped row, a wrong count, or a
;;; wrong verdict fails the check.
;;;
;;; docs/ is untracked (.gitignore holds "docs"), so a fresh clone has
;;; no kb.org and no milestone-overview.org.  When a doc file is absent,
;;; an INFO line is printed and the check is skipped, not failed.
;;;
;;; All checks read files, so the corpus needs no C entry point and is
;;; batch-safe.
;;;
;;; The repo root is bound by the .el wrapper as %m35-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test and
;;; prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m35-imp3.el.

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

(define (contains? text needle)
  ;; string-contains returns the match index or #f; normalize to a boolean
  ;; so `check' can compare against #t/#f.
  (and (string? text)
       (if (string-contains text needle) #t #f)))

(define (word-char? c)
  "True when C is an identifier character (letter, digit, or underscore)."
  (or (char-alphabetic? c) (char-numeric? c) (char=? c #\_)))

(define (contains-token? text token)
  "True when TOKEN occurs in TEXT as a whole identifier: no identifier
character on either side.  This matches the grep form \\bNAME\\b, so the
dispatcher xdisp_push_kboard does not count as push_kboard."
  (if (not (string? text))
      #f
      (let ((n (string-length token))
            (len (string-length text)))
        (let loop ((i 0))
          (if (> (+ i n) len)
              #f
              (if (and (string=? token (substring text i (+ i n)))
                       (or (= i 0)
                           (not (word-char? (string-ref text (1- i)))))
                       (or (= (+ i n) len)
                           (not (word-char? (string-ref text (+ i n))))))
                  #t
                  (loop (1+ i))))))))

(define (count-substr text needle)
  "Count the non-overlapping occurrences of NEEDLE in TEXT."
  (if (not (string? text))
      0
      (let loop ((i 0) (n 0))
        (let ((hit (string-contains text needle i)))
          (if hit
              (loop (+ hit (string-length needle)) (1+ n))
              n)))))

(define (count-prefix text prefix)
  "Count the lines of TEXT that start with PREFIX.  This is the anchored
count -- a loose substring match would also count a comment line."
  (if (not (string? text))
      0
      (call-with-input-string text
        (lambda (port)
          (let loop ((n 0))
            (let ((line (read-line port)))
              (cond ((eof-object? line) n)
                    ((string-prefix? prefix line) (loop (1+ n)))
                    (else (loop n)))))))))

(define (count-lines-with text needle)
  "Count the lines of TEXT that contain NEEDLE.  This mirrors the grep
form `grep -rn 'NEEDLE'` (one count per matching line)."
  (if (not (string? text))
      0
      (call-with-input-string text
        (lambda (port)
          (let loop ((n 0))
            (let ((line (read-line port)))
              (cond ((eof-object? line) n)
                    ((string-contains line needle) (loop (1+ n)))
                    (else (loop n)))))))))

(define (src-site-count)
  "Count the lines in every src/*.c and src/*.h file that mention
scm_c_public_ref.  This is the recorded brief.org §3 method:
`grep -rn 'scm_c_public_ref' src/*.c src/*.h`."
  (let ((dir (repo "src")))
    (if (not (file-exists? dir))
        0
        (let loop ((names (scandir dir
                                   (lambda (name)
                                     (or (string-suffix? ".c" name)
                                         (string-suffix? ".h" name)))))
                   (n 0))
          (if (null? names)
              n
              (loop (cdr names)
                    (+ n (count-lines-with
                          (slurp (string-append dir "/" (car names)))
                          "scm_c_public_ref"))))))))

(define (comma-format n)
  "Format integer N with thousands separators: 11338 -> \"11,338\"."
  (let* ((s (number->string n))
         (len (string-length s)))
    (let loop ((i len) (acc ""))
      (if (<= i 0)
          acc
          (let ((start (max 0 (- i 3))))
            (loop start
                  (string-append (substring s start i)
                                 (if (string=? acc "") "" ",")
                                 acc)))))))

(define (repo path) (string-append %m35-root "/" path))

(define (split-lines text)
  "Return the lines of TEXT as a list."
  (call-with-input-string text
    (lambda (port)
      (let loop ((acc '()))
        (let ((line (read-line port)))
          (if (eof-object? line) (reverse acc) (loop (cons line acc))))))))

(define (paragraphs text)
  "Split TEXT into paragraphs: each is a list of consecutive non-blank
lines.  A blank line separates paragraphs."
  (if (not (string? text))
      '()
      (let loop ((lines (split-lines text)) (cur '()) (acc '()))
        (cond ((null? lines)
               (reverse (if (null? cur) acc (cons (reverse cur) acc))))
              ((string-null? (string-trim (car lines)))
               (loop (cdr lines) '() (if (null? cur) acc (cons (reverse cur) acc))))
              (else (loop (cdr lines) (cons (car lines) cur) acc))))))

(define (paragraph-naming text token)
  "Return the first paragraph of TEXT that contains TOKEN, joined with
newlines, or #f.  The value must sit in the paragraph that names the
metric, not merely anywhere in the section (cr.org F2)."
  (let loop ((ps (paragraphs text)))
    (cond ((null? ps) #f)
          ((string-contains (string-join (car ps) "\n") token)
           (string-join (car ps) "\n"))
          (else (loop (cdr ps))))))

(define (stars line)
  "Return the number of leading '*' characters in LINE."
  (let loop ((i 0))
    (if (and (< i (string-length line)) (char=? (string-ref line i) #\*))
        (loop (1+ i)) i)))

(define (heading-line? line)
  "True when LINE is an org-mode heading: stars, then a space."
  (let ((n (stars line)))
    (and (> n 0)
         (< n (string-length line))
         (char=? (string-ref line n) #\space))))

(define (org-section text heading)
  "Return the org-mode section of TEXT introduced by the heading line
that starts with HEADING, up to but not including the next heading line
at the same or a shallower level.  Return #f when no such heading line
is present.  Scoping a check to one section stops text from another
milestone, or from a plan, from satisfying it."
  (and (string? text)
       (let* ((ls (split-lines text))
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

(define (line-with text needle)
  "Return the first line of TEXT that contains NEEDLE, or #f."
  (and (string? text)
       (call-with-input-string text
         (lambda (port)
           (let loop ()
             (let ((line (read-line port)))
               (cond ((eof-object? line) #f)
                     ((string-contains line needle) line)
                     (else (loop)))))))))

(define (line-n text n)
  "Return the 1-based Nth line of TEXT, or #f."
  (and (string? text)
       (let ((ls (split-lines text)))
         (and (>= (length ls) n) (list-ref ls (1- n))))))

(define (tracks-milestone? text tag)
  "True when TEXT's first org heading starts with TAG, for example
\"* M35\".  milestone.org is the live tracker and holds only the current
milestone.  This test lets a later milestone rewrite skip a historical
check instead of failing it."
  (and (string? text)
       (let ((ls (split-lines text)))
         (and (pair? ls) (string-prefix? tag (car ls))))))

(define (files-with-token dir suffix token)
  "Names of the files in DIR whose name ends with SUFFIX and whose text
holds TOKEN as a whole identifier.  This mirrors the scan
`rg -l '\\bTOKEN\\b' DIR`."
  (if (not (file-exists? dir))
      '()
      (let loop ((names (scandir dir (lambda (n) (string-suffix? suffix n))))
                 (acc '()))
        (if (null? names)
            (reverse acc)
            (let ((p (string-append dir "/" (car names))))
              (loop (cdr names)
                    (if (contains-token? (slurp p) token)
                        (cons (car names) acc)
                        acc)))))))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m35-root))
    (begin (report "m35/imp3/root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m35-root "."))
    (report "m35/imp3/root-bound" 'PASS))

(define kbd        (slurp (repo "src/keyboard.c")))
(define kg         (slurp (repo "src/keyboard-globals.c")))
(define kbd-h      (slurp (repo "src/keyboard.h")))
(define lisp-h     (slurp (repo "src/lisp.h")))
(define xdisp-c    (slurp (repo "src/xdisp.c")))
(define frame-c    (slurp (repo "src/frame.c")))
(define emacs-c    (slurp (repo "src/emacs.c")))
(define xmenu-c    (slurp (repo "src/xmenu.c")))
(define pgtkmenu-c (slurp (repo "src/pgtkmenu.c")))
(define xterm-c    (slurp (repo "src/xterm.c")))
(define pgtk-c     (slurp (repo "src/pgtkterm.c")))
(define process-c  (slurp (repo "src/process.c")))
(define dbusbind-c (slurp (repo "src/dbusbind.c")))
(define config-h   (slurp (repo "src/config.h")))

;;; --- 1. The anchored counts ---------------------------------------
;;; The brief.org §3 method.  The measured values are the M35 end state:
;;; keyboard.c 11,305, keyboard-globals.c 490, combined 11,795, DEFUNs
;;; 449, --=-shims 423, scm_c_public_ref sites 155.  (M36 imp-1
;;; re-measured: the two retired stubs leave keyboard.c.)
(if (not kbd)
    (report "m35/imp3/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      (check "m35/imp3/count/keyboard.c-lines" 11305
             (count-substr kbd "\n"))
      (check "m35/imp3/count/keyboard.c-defuns" 449
             (count-prefix kbd "DEFUN (\""))
      (check "m35/imp3/count/keyboard.c-shims" 423
             (count-prefix kbd "DEFUN (\"--"))))
(if (not kg)
    (report "m35/imp3/scan/keyboard-globals.c" (cons 'FAIL "missing"))
    (check "m35/imp3/count/keyboard-globals.c-lines" 490
           (count-substr kg "\n")))
(check "m35/imp3/count/combined-lines" 11795
       (+ (count-substr kbd "\n") (count-substr kg "\n")))
(check "m35/imp3/count/scm-c-public-ref-sites" 155
       (src-site-count))
;; A detail check: keyboard.c holds 73 of the sites.
(if (not kbd)
    (report "m35/imp3/scan/keyboard.c-sites" (cons 'FAIL "missing"))
    (check "m35/imp3/count/keyboard.c-sites" 71
           (count-lines-with kbd "scm_c_public_ref")))

;;; --- 2. The budget ------------------------------------------------
;;; The M31 re-based budget is combined 11,960.  Assert the combined
;;; surface is at or under it, and print the margin as INFO.
(define combined (+ (count-substr kbd "\n") (count-substr kg "\n")))
(check "m35/imp3/budget/under-11960" #t
       (<= combined 11960))
(info "m35/imp3/budget/margin" (- 11960 combined))

;;; --- 3. The three M34 retirements stay gone -----------------------
;;; No definition, no extern, no live caller.  A comment mention alone
;;; is not a caller.  contains-token? keeps xdisp_push_kboard apart from
;;; push_kboard and frame_maybe_not_single_kboard_state apart from
;;; not_single_kboard_state.
(check "m35/imp3/retired/safe-run-hooks-2/keyboard.c" #f
       (contains-token? kbd "safe_run_hooks_2"))
(check "m35/imp3/retired/safe-run-hooks-2/lisp.h" #f
       (contains-token? lisp-h "safe_run_hooks_2"))
(check "m35/imp3/retired/safe-run-hooks-2/xdisp.c" #f
       (contains-token? xdisp-c "safe_run_hooks_2"))
(check "m35/imp3/retired/push-kboard/keyboard.c" #f
       (contains-token? kbd "push_kboard"))
(check "m35/imp3/retired/push-kboard/keyboard.h" #f
       (contains-token? kbd-h "push_kboard"))
;; xdisp.c keeps the dispatcher xdisp_push_kboard, a different
;; identifier, so the whole-token scan must not find push_kboard.
(check "m35/imp3/retired/push-kboard/xdisp.c" #f
       (contains-token? xdisp-c "push_kboard"))
(check "m35/imp3/retired/not-single/keyboard.c" #f
       (contains-token? kbd "not_single_kboard_state"))
(check "m35/imp3/retired/not-single/keyboard.h" #f
       (contains-token? kbd-h "not_single_kboard_state"))
(check "m35/imp3/retired/not-single/frame.c" #f
       (contains-token? frame-c "not_single_kboard_state"))

;;; --- 4. The nine residual stubs keep a live buildable C caller ----
;;; One check per stub.  The caller is in a buildable .c file.  An NS
;;; file does not count: HAVE_NS is undefined (src/config.h).  The
;;; definitions stay in keyboard.c (see test-m35-imp2.scm).
(check "m35/imp3/ns/have-ns-undefined" #t
       (contains? config-h "/* #undef HAVE_NS */"))
(check "m35/imp3/keep/pop-kboard" #t
       (contains? kbd "pop_kboard ();"))
(check "m35/imp3/keep/safe-run-hooks/emacs.c" #t
       (contains? emacs-c "safe_run_hooks (Qkill_emacs_hook)"))
(check "m35/imp3/keep/safe-run-hooks/xmenu.c" #t
       (contains? xmenu-c "safe_run_hooks (Qactivate_menubar_hook)"))
(check "m35/imp3/keep/safe-run-hooks/pgtkmenu.c" #t
       (contains? pgtkmenu-c "safe_run_hooks (Qmenu_bar_update_hook)"))
;; M36 imp-1 retired swallow_events and timer_check.
(check "m35/imp3/keep/swallow-events-retired" #f
       (contains? process-c "swallow_events (do_display)"))
(check "m35/imp3/keep/gen-help-event/xterm.c" #t
       (contains? xterm-c "gen_help_event (Qnil, frame, Qnil, Qnil, 0)"))
(check "m35/imp3/keep/gen-help-event/pgtkterm.c" #t
       (contains? pgtk-c "gen_help_event (Qnil, frame_obj, Qnil, Qnil, 0)"))
(check "m35/imp3/keep/detect-input-pending" #t
       (contains? process-c "detect_input_pending ()"))
(check "m35/imp3/keep/detect-input-pending-run-timers" #t
       (contains? process-c "detect_input_pending_run_timers (do_display)"))
(check "m35/imp3/keep/timer-check-retired" #f
       (contains? process-c "timer_check ()"))
(check "m35/imp3/keep/gobble-input" #t
       (contains? kbd "gobble_input ()"))
(check "m35/imp3/keep/kbd-buffer-store-event" #t
       (contains? dbusbind-c "kbd_buffer_store_event (&event)"))

;;; --- 5. Census correction: kbd_buffer_store_event caller files ----
;;; 15 caller files: 14 buildable (.c) plus 1 NS (.m, nsterm.m).  The
;;; scan matches the name anywhere, so keyboard.c (the definition, no
;;; live call) is subtracted by hand.
(define kbds-c (files-with-token (repo "src") ".c" "kbd_buffer_store_event"))
(define kbds-m (files-with-token (repo "src") ".m" "kbd_buffer_store_event"))
(info "m35/imp3/census/kbd-buffer-store-event/.c-files" (length kbds-c))
(info "m35/imp3/census/kbd-buffer-store-event/.m-files" (length kbds-m))
(check "m35/imp3/census/kbd-buffer-store-event/buildable-callers" 14
       (- (length kbds-c) 1))            ; keyboard.c holds the definition
(check "m35/imp3/census/kbd-buffer-store-event/ns-callers" 1
       (length kbds-m))
(check "m35/imp3/census/kbd-buffer-store-event/total-caller-files" 15
       (+ (- (length kbds-c) 1) (length kbds-m)))
(check "m35/imp3/census/kbd-buffer-store-event/ns-is-nsterm" #t
       (if (member "nsterm.m" kbds-m) #t #f))
(check "m35/imp3/census/kbd-buffer-store-event/keyboard.c-no-call" #f
       (contains? kbd "kbd_buffer_store_event (&"))

;;; --- 6. Static: the corpus is registered in the keyboard group ----
(define run-tests (slurp (repo "tool/run-tests.scm")))

(define (line-index-with lines needle)
  "Index of the first line of LINES that contains NEEDLE, or #f."
  (list-index (lambda (l) (string-contains l needle)) lines))

(define (group-close-index lines start)
  "Index of the first line at or after START whose text is only a
closing paren, or #f.  The keyboard group is flat, so this is its end."
  (let loop ((i start))
    (cond ((>= i (length lines)) #f)
          ((equal? ")" (string-trim (list-ref lines i))) i)
          (else (loop (1+ i))))))

(let* ((rt-lines (and run-tests (split-lines run-tests)))
       (kg-start (and rt-lines
                      (line-index-with rt-lines "(group ; keyboard.c")))
       (kg-end (and kg-start (group-close-index rt-lines (1+ kg-start))))
       (reg-idx (and rt-lines
                     (line-index-with rt-lines
                                      "\"test/keyboard/test-m35-imp3.el\""))))
  (check "m35/imp3/run-tests.scm/registers-el" #t
         (and (string? run-tests)
              (and reg-idx
                   (contains? (list-ref rt-lines reg-idx)
                              "\"test/keyboard/test-m35-imp3.el\""))
              (and kg-end
                   (< kg-start reg-idx)
                   (< reg-idx kg-end)))))

;;; --- 7. The guard test of imp-1 stays correct ---------------------
;;; brief.org §5.2 item 7.  The two current-line-number anchors must
;;; stay current.  imp-1 repaired them and pinned them; imp-3 keeps them
;;; correct.  Check the live comment line, not a prose phrase.
(check "m35/imp3/imp1/xdisp.c:582" #t
       (contains? (line-n xdisp-c 582) "(src/xdisp.c:27788, :28574)"))
(check "m35/imp3/imp1/keyboard.c:3927" #t
       (contains? (line-n kbd 3927) "(term.c:3595)"))
(check "m35/imp3/imp1/corpus-registered" #t
       (contains? run-tests "\"test/keyboard/test-m35-imp1.el\""))

;;; --- 8. Static: the accounting is recorded ------------------------
;;; docs/ is untracked, so a fresh clone has no kb.org and no
;;; milestone-overview.org.  When a doc file is absent, print an INFO
;;; line instead of a FAIL: the check is skipped, not failed.
;;;
;;; The counts check (brief.org §5.2 item 1): each measured value must
;;; equal the value recorded in the doc.
(define (doc-metric label section key name value)
  "Check that the paragraph of SECTION that names NAME also holds VALUE.
This is a name-plus-value check: the value must sit in the paragraph
that names the metric, so a value in unrelated prose does not pass
(cr.org F2, brief.org §5.2 item 1)."
  (let ((para (paragraph-naming section name)))
    (check (string-append label "/" key) #t
           (and para (string-contains para value) #t))))

(define (doc-records-counts label section)
  "For each measured count, find the paragraph in SECTION that names the
metric, and require the formatted value in that same paragraph.  This
is stronger than a whole-section substring match (cr.org F2)."
  (doc-metric label section "keyboard.c-lines"
              "keyboard.c" (comma-format (count-substr kbd "\n")))
  (doc-metric label section "keyboard-globals.c-lines"
              "keyboard-globals.c" (comma-format (count-substr kg "\n")))
  ;; The combined total sits with keyboard-globals.c in every record.
  (doc-metric label section "combined-lines"
              "keyboard-globals.c" (comma-format combined))
  (doc-metric label section "scm-c-public-ref-sites"
              "scm_c_public_ref" (comma-format (src-site-count))))

(define kb (slurp (repo "docs/kb.org")))
(if (not kb)
    (info "m35/imp3/kb.org/skipped" "docs/kb.org absent (untracked)")
    (let ((kb-m35 (org-section kb "** M35")))
      (if (not kb-m35)
          (report "m35/imp3/kb.org/status-closed"
                  (cons 'FAIL "no ** M35 section in docs/kb.org"))
          (begin
            (check "m35/imp3/kb.org/status-closed" #t
                   (contains? kb-m35 "status :: closed"))
            (check "m35/imp3/kb.org/imp3-record" #t
                   (contains? kb-m35 "imp-3 ("))
            (doc-records-counts "m35/imp3/kb.org/count" kb-m35)))))

(define overview (slurp (repo "docs/milestone-overview.org")))
(if (not overview)
    (info "m35/imp3/overview/skipped"
          "docs/milestone-overview.org absent (untracked)")
    (let ((ov-m35 (org-section overview "*** M35")))
      (if (not ov-m35)
          (report "m35/imp3/overview/m35-closed"
                  (cons 'FAIL "no *** M35 section in the overview"))
          (begin
            (check "m35/imp3/overview/m35-closed" #t
                   (contains? ov-m35 "CLOSED"))
            (doc-records-counts "m35/imp3/overview/count" ov-m35)))))

(define milestone (slurp (repo "milestone.org")))
(cond
 ((not milestone)
  (info "m35/imp3/milestone.org/skipped" "milestone.org absent (untracked)"))
 ((not (tracks-milestone? milestone "* M35"))
  ;; milestone.org is the live tracker and holds only the current
  ;; milestone.  A later milestone rewrite drops the M35 brief.  Pin it
  ;; only while it still tracks M35; else skip.
  (info "m35/imp3/milestone.org/skipped"
        "milestone.org no longer tracks M35 (live tracker)"))
 (else
  (let ((ms-status (org-section milestone "** Status"))
        (ms-imps (org-section milestone "** Imps"))
        (ms-stands (org-section milestone "** Where the port stands")))
    (check "m35/imp3/milestone.org/status-closed" #t
           (and (contains? ms-status "closed")
                (contains? ms-status "imp-3")))
    (check "m35/imp3/milestone.org/imp3-done" #t
           (and (contains? ms-imps "imp-3")
                (contains? ms-imps "DONE")))
    (doc-records-counts "m35/imp3/milestone.org/count" ms-stands))))

;;; --- 9. Self-test of the name-plus-value matcher ------------------
;;; The cr.org F2 fix: the doc count check reads the name and the value
;;; in one paragraph.  Guard the matcher itself, so a future edit that
;;; weakens it back to a whole-section substring match fails here.
(define (paragraph-hit? doc token value)
  (let ((p (paragraph-naming doc token)))
    (and p (string-contains p value) #t)))
(check "m35/imp3/selftest/name-and-value-same-paragraph" #t
       (paragraph-hit? "intro\n\nkeyboard.c holds 11,338 lines\ndone\n"
                       "keyboard.c" "11,338"))
(check "m35/imp3/selftest/value-in-other-paragraph" #f
       (paragraph-hit? "keyboard.c line\n\n11,338 elsewhere\n"
                       "keyboard.c" "11,338"))
(check "m35/imp3/selftest/paragraph-isolated" #t
       (equal? (paragraph-naming "foo keyboard.c\n\nbar 99\n" "keyboard.c")
               "foo keyboard.c"))
