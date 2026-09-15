;;; test-m33-imp7.scm --- M33 imp-7: the close-out audit corpus.
;;;
;;; brief.org (M33 imp-7) is the docs-only close-out.  It runs no port
;;; work.  It re-measures the surface (Job 1) and proves the two stub
;;; retirements (Job 2).  This corpus pins the Job 2 proof and the Job 1
;;; anchored counts so the close-out claims are checked automatically
;;; instead of only by hand.
;;;
;;; Two kinds of check:
;;;
;;;   - a static retirement proof: show_help_echo and
;;;     discard_mouse_events have no definition, extern, or caller left;
;;;     the file-local static tty_menu_discard_mouse_events stays in
;;;     term.c; the four stay-C stubs keep their stated caller; and the
;;;     two migrated names have no C storage in the generated globals.h.
;;;   - a static count check: the anchored Job 1 numbers (the
;;;     keyboard.c DEFUN count and the keyboard-globals.c site split)
;;;     match the brief table.
;;;
;;; All checks read files, so the corpus needs no C entry point and is
;;; batch-safe.
;;;
;;; The repo root is bound by the .el wrapper as %m33-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test and
;;; prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m33-imp7.el.

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

(define (repo path) (string-append %m33-root "/" path))

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
\"* M33\".  milestone.org is the live tracker and holds only the current
milestone (cr.org F1).  This test lets a later milestone rewrite skip a
historical check instead of failing it."
  (and (string? text)
       (let ((ls (split-lines text)))
         (and (pair? ls) (string-prefix? tag (car ls))))))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m33-root))
    (begin (report "m33/imp7/root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m33-root "."))
    (report "m33/imp7/root-bound" 'PASS))

;;; --- 1. Static: show_help_echo is fully retired --------------------
;;; imp-2 retired the stub.  No definition, no extern, no caller may
;;; stay in the three files the brief names.  The allowed comment at
;;; keyboard.c:1072 stays (it records the retirement).
(define kbd (slurp (repo "src/keyboard.c")))
(if (not kbd)
    (report "m33/imp7/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      ;; No call site and no definition (the comment has no " (").
      (check "m33/imp7/keyboard.c/show-help-echo/no-call" #f
             (contains? kbd "show_help_echo ("))
      (check "m33/imp7/keyboard.c/show-help-echo/no-definition" #f
             (contains? kbd "show_help_echo (Lisp_Object"))
      ;; The allowed comment stays.
      (check "m33/imp7/keyboard.c/show-help-echo/keeps-comment" #t
             (contains? kbd "show_help_echo's"))))

(define kbd-h (slurp (repo "src/keyboard.h")))
(if (not kbd-h)
    (report "m33/imp7/scan/keyboard.h" (cons 'FAIL "src/keyboard.h missing"))
    (check "m33/imp7/keyboard.h/no-show-help-echo" #f
           (contains? kbd-h "show_help_echo")))

(define lisp-h (slurp (repo "src/lisp.h")))
(if (not lisp-h)
    (report "m33/imp7/scan/lisp.h" (cons 'FAIL "src/lisp.h missing"))
    (check "m33/imp7/lisp.h/no-show-help-echo" #f
           (contains? lisp-h "show_help_echo")))

;;; --- 2. Static: discard_mouse_events is fully retired --------------
;;; imp-1 retired the stub.  No call, no definition, no extern.  The new
;;; file-local static tty_menu_discard_mouse_events is a different
;;; symbol; it stays in term.c.
(if (not kbd)
    (report "m33/imp7/scan/keyboard.c-discard"
            (cons 'FAIL "src/keyboard.c missing"))
    (begin
      (check "m33/imp7/keyboard.c/discard-mouse-events/no-call" #f
             (contains? kbd "discard_mouse_events ("))
      (check "m33/imp7/keyboard.c/discard-mouse-events/no-definition" #f
             (contains? kbd "discard_mouse_events (void)"))
      ;; The allowed comment at keyboard.c:3960 stays.
      (check "m33/imp7/keyboard.c/discard-mouse-events/keeps-comment" #t
             (contains? kbd "discard_mouse_events stub retired"))))

(if (not kbd-h)
    (report "m33/imp7/scan/keyboard.h-discard"
            (cons 'FAIL "src/keyboard.h missing"))
    (check "m33/imp7/keyboard.h/no-discard-mouse-events" #f
           (contains? kbd-h "discard_mouse_events")))

(if (not lisp-h)
    (report "m33/imp7/scan/lisp.h-discard" (cons 'FAIL "src/lisp.h missing"))
    (check "m33/imp7/lisp.h/no-discard-mouse-events" #f
           (contains? lisp-h "discard_mouse_events")))

;;; --- 3. Static: the new static stays in term.c ---------------------
(define term-c (slurp (repo "src/term.c")))
(if (not term-c)
    (report "m33/imp7/scan/term.c" (cons 'FAIL "src/term.c missing"))
    (begin
      (check "m33/imp7/term.c/defines-static" #t
             (contains? term-c "tty_menu_discard_mouse_events (void)"))
      (check "m33/imp7/term.c/calls-static" #t
             (contains? term-c "tty_menu_discard_mouse_events ();"))))

;;; --- 4. Static: the four stay-C stubs keep their caller ------------
;;; brief.org Job 2 "Confirm the four non-retirements".  Each must still
;;; have its stated caller.  M34 imp-1 moved the dispnew.c callers of
;;; gen_help_event and detect_input_pending into (emacs display); the
;;; stubs stay C because their non-M34 callers remain (process.c for
;;; detect_input_pending; xterm.c/pgtkterm.c for gen_help_event).
(define dispnew-c (slurp (repo "src/dispnew.c")))
(if (not dispnew-c)
    (report "m33/imp7/scan/dispnew.c" (cons 'FAIL "src/dispnew.c missing"))
    (begin
      (check "m33/imp7/moved/gen-help-event-dispnew" #f
             (contains? dispnew-c "gen_help_event (help_echo_string"))
      (check "m33/imp7/moved/detect-input-pending-dispnew" #f
             (contains? dispnew-c "detect_input_pending ()"))))

(define process-c (slurp (repo "src/process.c")))
(if (not process-c)
    (report "m33/imp7/scan/process.c" (cons 'FAIL "src/process.c missing"))
    (begin
      ;; M36 imp-2 retired the stub and moved the decision to
      ;; (emacs process-wait).
      (check "m33/imp7/stays-c/detect-input-pending-process-retired" #f
             (contains? process-c "detect_input_pending ()"))
      ;; M36 imp-1 retired the stub and moved the decision to
      ;; (emacs process-wait).
      (check "m33/imp7/stays-c/swallow-events-retired" #f
             (contains? process-c "swallow_events (do_display)"))))

(define nsmenu-m (slurp (repo "src/nsmenu.m")))
(check "m33/imp7/stays-c/timer-check-ns" #t
       (contains? nsmenu-m "timer_check ()"))

;;; --- 5. Static: the two migrated names have no C storage -----------
;;; A DEFVAR_* value cell would make the name C-owned again.  The check
;;; reads the generated globals.h, which is what a fresh build produces.
(define gh (slurp (repo "src/globals.h")))
(if (not gh)
    (report "m33/imp7/scan/globals.h" (cons 'FAIL "src/globals.h missing"))
    (begin
      (check "m33/imp7/no-cell/f-extra-keyboard-modifiers" #f
             (contains? gh "f_extra_keyboard_modifiers"))
      (check "m33/imp7/no-cell/f-mwheel-coalesce-scroll-events" #f
             (contains? gh "f_mwheel_coalesce_scroll_events"))))

;;; --- 6. INFO: the durable NS reader caveat -------------------------
;;; src/nsterm.m still reads the deleted mwheel_coalesce_scroll_events
;;; cell.  NS is not built, so the build does not show the break.  This
;;; is recorded, not asserted against the supported build.
(define nsterm-m (slurp (repo "src/nsterm.m")))
(info "m33/imp7/info/ns-mwheel-readers"
      (count-substr nsterm-m "mwheel_coalesce_scroll_events"))

;;; --- 7. Static: the anchored Job 1 counts --------------------------
;;; The brief warns twice about loose patterns.  Use the anchored forms
;;; only: "^DEFUN (\"" for the DEFUN count and "^  DEFVAR_*/DEFSYM (" for
;;; the site counts.  M33 added no new keyboard.c primitive.  M34 imp-1
;;; added one (--detect-input-pending-run-timers), so the count reached
;;; 449; M36 imp-2 retired three DEFUNs, so the count is 446.
;;; and imp-6 moved extra-keyboard-modifiers (INT) and
;;; mwheel-coalesce-scroll-events (BOOL) to Scheme, so the DEFVAR_INT and
;;; DEFVAR_BOOL site counts are 1 each.
(if (not kbd)
    (report "m33/imp7/scan/keyboard.c-count" (cons 'FAIL "missing"))
    (check "m33/imp7/count/keyboard.c-defuns" 446
           (count-prefix kbd "DEFUN (\"")))

;;; --- 8. Static: keyboard-globals.c keeps the anchored split --------
(define kg (slurp (repo "src/keyboard-globals.c")))
(if (not kg)
    (report "m33/imp7/scan/keyboard-globals.c" (cons 'FAIL "missing"))
    (begin
      (check "m33/imp7/count/defvar-lisp" 32 (count-prefix kg "  DEFVAR_LISP ("))
      (check "m33/imp7/count/defvar-int" 1 (count-prefix kg "  DEFVAR_INT ("))
      (check "m33/imp7/count/defvar-bool" 1 (count-prefix kg "  DEFVAR_BOOL ("))
      (check "m33/imp7/count/defvar-kboard" 8 (count-prefix kg "  DEFVAR_KBOARD ("))
      (check "m33/imp7/count/defsym" 34 (count-prefix kg "  DEFSYM ("))))

;;; --- 9. Static: the corpus is registered ---------------------------
;;; Match the whole registration line: the quoted path AND one word of
;;; the trailing comment.  A bare substring cannot detect a wrong group,
;;; a bad path, or a missing comment (cr.org F5).
(define run-tests (slurp (repo "tool/run-tests.scm")))
(define reg-line (line-with run-tests "test/keyboard/test-m33-imp7.el"))
(check "m33/imp7/run-tests.scm/registers-el" #t
       (and (contains? reg-line "\"test/keyboard/test-m33-imp7.el\"")
            (contains? reg-line "close-out audit")))

;;; --- 10. Static: the accounting is recorded ------------------------
;;; Job 4 records the close-out.  Each check is scoped to its section
;;; only: a whole-file search is satisfied by text from another
;;; milestone, or from a plan, so it cannot prove the M33 record
;;; (cr.org F1).
;;;
;;; docs/ is untracked (.gitignore holds "docs"), so a fresh clone has
;;; no kb.org and no milestone-overview.org.  When a doc file is absent,
;;; print an INFO line instead of a FAIL: the check is skipped, not
;;; failed (cr.org F4).
(define kb (slurp (repo "docs/kb.org")))
(if (not kb)
    (info "m33/imp7/kb.org/skipped" "docs/kb.org absent (untracked)")
    (let ((kb-m33 (org-section kb "** M33")))
      (if (not kb-m33)
          (report "m33/imp7/kb.org/status-closed"
                  (cons 'FAIL "no ** M33 section in docs/kb.org"))
          (begin
            (check "m33/imp7/kb.org/status-closed" #t
                   (contains? kb-m33 "status :: closed"))
            (check "m33/imp7/kb.org/imp7-note" #t
                   (contains? kb-m33 "imp-7 (2026-09-13; the close-out"))))))

(define overview (slurp (repo "docs/milestone-overview.org")))
(if (not overview)
    (info "m33/imp7/overview/skipped"
          "docs/milestone-overview.org absent (untracked)")
    (let ((ov-m33 (org-section overview "*** M33")))
      (if (not ov-m33)
          (report "m33/imp7/overview/m33-closed"
                  (cons 'FAIL "no *** M33 section in the overview"))
          (begin
            (check "m33/imp7/overview/m33-closed" #t
                   (contains? ov-m33
                              "terminal read path + help/menu (CLOSED 2026-09-13"))
            (check "m33/imp7/overview/swallow-events-correction" #t
                   (contains? ov-m33 "swallow_events= has *no* M33-file"))))))

(define milestone (slurp (repo "milestone.org")))
(cond
 ((not milestone)
  (info "m33/imp7/milestone.org/skipped" "milestone.org absent (untracked)"))
 ((not (tracks-milestone? milestone "* M33"))
  ;; milestone.org is the live tracker and holds only the current
  ;; milestone (cr.org F1).  A later milestone rewrite drops the M33
  ;; brief.  Pin it only while it still tracks M33; else skip.
  (info "m33/imp7/milestone.org/skipped"
        "milestone.org no longer tracks M33 (live tracker)"))
 (else
  (let ((ms-imp7 (org-section milestone "** imp-7")))
    (if (not ms-imp7)
        (report "m33/imp7/milestone.org/imp7"
                (cons 'FAIL "no ** imp-7 section in milestone.org"))
        (check "m33/imp7/milestone.org/imp7" #t
               (contains? ms-imp7
                          "test/keyboard/test-m33-imp7.{el,scm}"))))))
