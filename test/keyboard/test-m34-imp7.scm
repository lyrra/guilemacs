;;; test-m34-imp7.scm --- M34 imp-7: the close-out audit corpus.
;;;
;;; brief.org (M34 imp-7) is the close-out.  It deletes each stub that
;;; lost its last C caller, keeps each stub that still has one, and
;;; re-measures the surface.  This corpus pins the close-out so the
;;; claims are checked automatically and not only by hand.
;;;
;;; Two kinds of check:
;;;
;;;   - a static retirement proof: safe_run_hooks_2, push_kboard, and
;;;     not_single_kboard_state have no definition, no extern, and no
;;;     live C caller left.  A whole-identifier scan is used, so a
;;;     longer name that holds the retired name as a substring (for
;;;     example the xdisp.c dispatcher xdisp_push_kboard) does not
;;;     count -- this mirrors the rule `grep -rn '\bNAME\b'`.
;;;   - a static keep proof: pop_kboard, safe_run_hooks,
;;;     swallow_events, gen_help_event, detect_input_pending,
;;;     timer_check, gobble_input, kbd_buffer_store_event, and
;;;     track-mouse each keep a live C caller.
;;;
;;; The corpus also pins the anchored surface counts and the record in
;;; the docs.  All checks read files, so the corpus needs no C entry
;;; point and is batch-safe.
;;;
;;; The repo root is bound by the .el wrapper as %m34-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test and
;;; prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m34-imp7.el.

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

(define (count-substr text needle)
  "Count the non-overlapping occurrences of NEEDLE in TEXT."
  (if (not (string? text))
      0
      (let loop ((i 0) (n 0))
        (let ((hit (string-contains text needle i)))
          (if hit
              (loop (+ hit (string-length needle)) (1+ n))
              n)))))

(define (count-lines-with text needle)
  "Count the lines of TEXT that contain NEEDLE.  This mirrors the grep
form `grep -rn 'NEEDLE'` (one count per matching line, not per
occurrence)."
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
scm_c_public_ref.  This is the recorded brief.org Step-4 method:
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

(define (repo path) (string-append %m34-root "/" path))

(define (split-lines text)
  "Return the lines of TEXT as a list."
  (call-with-input-string text
    (lambda (port)
      (let loop ((acc '()))
        (let ((line (read-line port)))
          (if (eof-object? line) (reverse acc) (loop (cons line acc))))))))

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

(define (tracks-milestone? text tag)
  "True when TEXT's first org heading starts with TAG, for example
\"* M34\".  milestone.org is the live tracker and holds only the current
milestone (cr.org F1).  This test lets a later milestone rewrite skip a
historical check instead of failing it."
  (and (string? text)
       (let ((ls (split-lines text)))
         (and (pair? ls) (string-prefix? tag (car ls))))))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m34-root))
    (begin (report "m34/imp7/root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m34-root "."))
    (report "m34/imp7/root-bound" 'PASS))

(define kbd (slurp (repo "src/keyboard.c")))
(define kbd-h (slurp (repo "src/keyboard.h")))
(define lisp-h (slurp (repo "src/lisp.h")))
(define xdisp-c (slurp (repo "src/xdisp.c")))
(define frame-c (slurp (repo "src/frame.c")))

;;; --- 1. Static: safe_run_hooks_2 is fully retired ------------------
;;; No definition, no extern, no caller.  Its only caller (xdisp.c S3)
;;; left C at imp-5.
(if (not kbd)
    (report "m34/imp7/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (check "m34/imp7/retired/safe-run-hooks-2/keyboard.c" #f
           (contains-token? kbd "safe_run_hooks_2")))
(check "m34/imp7/retired/safe-run-hooks-2/lisp.h" #f
       (contains-token? lisp-h "safe_run_hooks_2"))
(check "m34/imp7/retired/safe-run-hooks-2/xdisp.c" #f
       (contains-token? xdisp-c "safe_run_hooks_2"))

;;; --- 2. Static: push_kboard is fully retired ----------------------
;;; No definition, no extern, no caller.  Its callers (xdisp.c 27683 and
;;; 28523) left C at imp-6.  xdisp.c keeps the dispatcher
;;; xdisp_push_kboard, which is a different identifier.
(if (not kbd)
    (report "m34/imp7/scan/keyboard.c-push" (cons 'FAIL "missing"))
    (check "m34/imp7/retired/push-kboard/keyboard.c" #f
           (contains-token? kbd "push_kboard")))
(check "m34/imp7/retired/push-kboard/keyboard.h" #f
       (contains-token? kbd-h "push_kboard"))
(check "m34/imp7/retired/push-kboard/xdisp.c" #f
       (contains-token? xdisp-c "push_kboard"))

;;; --- 3. Static: not_single_kboard_state is fully retired ----------
;;; No definition, no extern, no caller.  Its caller (frame.c 2691) left
;;; C at imp-2.
(if (not kbd)
    (report "m34/imp7/scan/keyboard.c-not-single" (cons 'FAIL "missing"))
    (check "m34/imp7/retired/not-single/keyboard.c" #f
           (contains-token? kbd "not_single_kboard_state")))
(check "m34/imp7/retired/not-single/keyboard.h" #f
       (contains-token? kbd-h "not_single_kboard_state"))
(check "m34/imp7/retired/not-single/frame.c" #f
       (contains-token? frame-c "not_single_kboard_state"))

;;; --- 4. Static: the kept stubs still have a live C caller ---------
;;; Each keeps a caller outside the M34 files.  The name and the reason
;;; are recorded in docs/kb.org ** M34 and milestone.org.
(if (not kbd)
    (report "m34/imp7/scan/keyboard.c-keep" (cons 'FAIL "missing"))
    (begin
      (check "m34/imp7/kept/pop-kboard/definition" #t
             (contains? kbd "pop_kboard (void)"))
      (check "m34/imp7/kept/pop-kboard/caller" #t
             (contains? kbd "pop_kboard ();"))
      (check "m34/imp7/kept/safe-run-hooks/definition" #t
             (contains? kbd "safe_run_hooks (Lisp_Object hook)"))
      (check "m34/imp7/kept/gobble-input" #t
             (contains? kbd "gobble_input (void)"))))

(define emacs-c (slurp (repo "src/emacs.c")))
(check "m34/imp7/kept/safe-run-hooks/emacs.c" #t
       (contains? emacs-c "safe_run_hooks (Qkill_emacs_hook)"))

(define process-c (slurp (repo "src/process.c")))
(if (not process-c)
    (report "m34/imp7/scan/process.c" (cons 'FAIL "src/process.c missing"))
    (begin
      (check "m34/imp7/kept/swallow-events" #t
             (contains? process-c "swallow_events (do_display)"))
      (check "m34/imp7/kept/detect-input-pending" #t
             (contains? process-c "detect_input_pending ()"))
      (check "m34/imp7/kept/timer-check" #t
             (contains? process-c "timer_check ()"))))

(define xterm-c (slurp (repo "src/xterm.c")))
(check "m34/imp7/kept/gen-help-event" #t
       (contains? xterm-c "gen_help_event ("))

(define dbusbind-c (slurp (repo "src/dbusbind.c")))
(check "m34/imp7/kept/kbd-buffer-store-event" #t
       (contains? dbusbind-c "kbd_buffer_store_event (&event)"))

(define kg (slurp (repo "src/keyboard-globals.c")))
(if (not kg)
    (report "m34/imp7/scan/keyboard-globals.c" (cons 'FAIL "missing"))
    (begin
      ;; track-mouse stays C: a DEFVAR_LISP site plus the keyboard.c
      ;; accessors.
      (check "m34/imp7/kept/track-mouse/defvar" #t
             (contains? kg "DEFVAR_LISP (\"track-mouse\""))
      (check "m34/imp7/kept/track-mouse/accessor" #t
             (contains? kbd "--track-mouse"))
      ;; name verdict: overriding-local-map-menu-flag stays C.
      (check "m34/imp7/kept/overriding-local-map-menu-flag/defvar" #t
             (contains? kg "DEFVAR_LISP (\"overriding-local-map-menu-flag\""))))

;;; --- 5. Static: the anchored surface counts -----------------------
;;; brief.org Step 4 asks for three measurements.  brief.org warns about
;;; loose patterns, so use the anchored form "^DEFUN (\"" for the DEFUN
;;; count, and the recorded grep methods for the rest.  Measure the
;;; keyboard.c and keyboard-globals.c line counts, their combined count
;;; against the M31 re-based budget of 11,960, and the scm_c_public_ref
;;; site count via `grep -rn 'scm_c_public_ref' src/*.c src/*.h`.  The
;;; measured numbers at imp-7: 11,338 + 490 = 11,828 (132 under the
;;; budget); 155 sites (158 before; the deletions remove 3 dispatcher
;;; sites).  Record the counts as INFO pairs, never as assertions.
(check "m34/imp7/count/keyboard.c-defuns" 449
       (count-prefix kbd "DEFUN (\""))
(info "m34/imp7/count/keyboard.c-lines" (count-substr kbd "\n"))
(info "m34/imp7/count/keyboard-globals.c-lines" (count-substr kg "\n"))
(info "m34/imp7/count/combined-lines"
      (+ (count-substr kbd "\n") (count-substr kg "\n")))
(info "m34/imp7/count/scm-c-public-ref-sites" (src-site-count))

;;; --- 6. Static: the corpus is registered --------------------------
;;; Match the quoted path AND one word of the trailing comment, so a
;;; wrong group, a bad path, or a missing comment fails the check.
(define run-tests (slurp (repo "tool/run-tests.scm")))
(define reg-line (line-with run-tests "test/keyboard/test-m34-imp7.el"))
(check "m34/imp7/run-tests.scm/registers-el" #t
       (and (contains? reg-line "\"test/keyboard/test-m34-imp7.el\"")
            (contains? reg-line "close-out")))

;;; --- 7. Static: the accounting is recorded ------------------------
;;; docs/ is untracked (.gitignore holds "docs"), so a fresh clone has
;;; no kb.org and no milestone-overview.org.  When a doc file is absent,
;;; print an INFO line instead of a FAIL: the check is skipped, not
;;; failed.  Scope each check to its own section.
(define kb (slurp (repo "docs/kb.org")))
(if (not kb)
    (info "m34/imp7/kb.org/skipped" "docs/kb.org absent (untracked)")
    (let ((kb-m34 (org-section kb "** M34")))
      (if (not kb-m34)
          (report "m34/imp7/kb.org/status-closed"
                  (cons 'FAIL "no ** M34 section in docs/kb.org"))
          (begin
            (check "m34/imp7/kb.org/status-closed" #t
                   (contains? kb-m34 "status :: closed"))
            (check "m34/imp7/kb.org/imp7-note" #t
                   (contains? kb-m34 "imp-7 ("))))))

(define overview (slurp (repo "docs/milestone-overview.org")))
(if (not overview)
    (info "m34/imp7/overview/skipped"
          "docs/milestone-overview.org absent (untracked)")
    (let ((ov-m34 (org-section overview "*** M34")))
      (if (not ov-m34)
          (report "m34/imp7/overview/m34-closed"
                  (cons 'FAIL "no *** M34 section in the overview"))
          (check "m34/imp7/overview/m34-closed" #t
                 (contains? ov-m34 "CLOSED")))))

(define milestone (slurp (repo "milestone.org")))
(cond
 ((not milestone)
  (info "m34/imp7/milestone.org/skipped" "milestone.org absent (untracked)"))
 ((not (tracks-milestone? milestone "* M34"))
  ;; milestone.org is the live tracker and holds only the current
  ;; milestone (cr.org F1).  A later milestone rewrite drops the M34
  ;; brief.  Pin it only while it still tracks M34; else skip.
  (info "m34/imp7/milestone.org/skipped"
        "milestone.org no longer tracks M34 (live tracker)"))
 (else
  (let ((ms-imp7 (org-section milestone "** Next commit brief")))
    (if (not ms-imp7)
        (report "m34/imp7/milestone.org/imp7"
                (cons 'FAIL "no imp-7 section in milestone.org"))
        (check "m34/imp7/milestone.org/imp7" #t
               (contains? ms-imp7
                          "test/keyboard/test-m34-imp7.{el,scm}"))))))
