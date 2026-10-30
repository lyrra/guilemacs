;;; test-m54-imp1.el --- M54 imp-1 TTY stream ownership audit corpus.
;;;
;;; M54 imp-1 is the TTY stream ownership AUDIT (brief.org section 1).
;;; It is docs only: the net C delta is 0 and the net Scheme delta is 0.
;;; It measures the boundary of the 3 src/termchar.h FILE * streams and
;;; records the A1 / A2 verdict (docs/m54-plan.org).
;;;
;;; This corpus pins the measured surface, the 3 stream fields, the
;;; src/term.c site map, and the registration in the tree, so a stale
;;; number or a missing registration fails the run.
;;;
;;; It pins these groups:
;;;
;;;   S1 -- REMOVED by M61 imp-2b (milestone.org findings F2).  S1 held
;;;         the source-text pins of src/term.c (lines, ^DEFUN ( count,
;;;         --tty-* leaf count, scm_c_public_ref sites), the
;;;         mod/emacs/tty-output.scm line count, and the tree-wide
;;;         scm_c_public_ref count.  A source-inspection test proves no
;;;         behavior, so the assertions are removed and NOT re-pinned
;;;         (docs/milestone-overview.org =Test rules for ports=,
;;;         docs/arch.org =Testing=).  The measured numbers live in the
;;;         commit message of M61 imp-2b.
;;;   S2 -- the 3 stream fields of src/termchar.h: input :51, output
;;;         :53, termscript :61 (name, FILE * type, and line), plus the
;;;         boundary rule ("one owner, one writer": no Guile port owns a
;;;         C FILE *).  S2 holds 4 checks.
;;;   S3 -- the src/term.c site map: the ordered name / line list of the
;;;         stream operations (the output / termscript writes, the
;;;         flushes, the read handle, the open / close, the init, and
;;;         the size query), the 4 --tty-* leaf DEFUNs, the two M52
;;;         writer helpers, and the lifecycle anchors.  S3 holds 4
;;;         checks.
;;;   S4 -- the registration: the corpus is registered in the (m54)
;;;         group of tool/run-tests.scm, after the (m53) group, and the
;;;         (m52) and (m53) groups stay present.  S4 holds 4 checks.
;;;   S5 -- the guards: a per-group min-count guard for S1 .. S4, and
;;;         the in-process group-total `ert-deftest'.  S5 holds 4
;;;         checks.
;;;
;;; This corpus reads TRACKED files only (src/, mod/, and the tracked
;;; runner tool/run-tests.scm).  It does NOT read docs/ (docs/kb.org
;;; test-must-not-read-docs): a gitignored record can only pass or skip,
;;; so a record check proves nothing.
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real FAIL, not a pass (brief.org section 2).  Every check
;;; registers a real ERT test via imp-register-bool-as-ert-test, so the
;;; harness parses the ERT output and the exit code is correct.

(princ "=== m54 imp-1 TTY stream ownership audit suite ===\n")

(require 'imp-ert-report)

(defvar m54-imp1--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m54-imp1--registered 0
  "Total number of checks this corpus has registered.")
(defvar m54-imp1--group nil
  "The group that `m54-imp1--check' counts into: `s1' .. `s5', or nil.")
(defvar m54-imp1--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m54-imp1--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m54-imp1--counts)) 0))

(defun m54-imp1--bump-group ()
  "Count one check into `m54-imp1--group'."
  (when m54-imp1--group
    (let ((cell (assq m54-imp1--group m54-imp1--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m54-imp1--group 1) m54-imp1--counts)))))

(defun m54-imp1--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m54-imp1-absent' when REL does not exist."
  (let ((path (expand-file-name rel m54-imp1--root)))
    (if (not (file-exists-p path))
        'm54-imp1-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m54-imp1--contains-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  An absent file
folds to nil, so a check prints FAIL: an absent src/ file is a real
error, not a pass (brief.org section 2)."
  (let ((hit (m54-imp1--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm54-imp1-absent)) (and hit t))))

(defun m54-imp1--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE.  REL is read
once, so a multi-needle check does not re-read the file per needle."
  (m54-imp1--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m54-imp1--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match.  This is the
ordered name list of brief.org section 6, preferred over a line pin."
  (m54-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m54-imp1--exists-p (rel)
  "Non-nil when the TRACKED file REL (repo-root-relative) exists."
  (file-exists-p (expand-file-name rel m54-imp1--root)))

(defun m54-imp1--line-of (rel regexp)
  "Return the 1-based line number of the first REGEXP match in REL, or
nil when REGEXP does not match.  The reader returns the symbol
`m54-imp1-absent' when REL does not exist, so the caller's `eql' folds
to nil and the check FAILS."
  (m54-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (when (re-search-forward regexp nil t)
        (let ((end (match-beginning 0)) (n 1))
          (goto-char (point-min))
          (while (search-forward "\n" end t) (setq n (1+ n)))
          n)))))

(defun m54-imp1--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
The count callers pass `(eql N value)': when the source file is absent
the reader returns the symbol `m54-imp1-absent', so `eql' yields nil and
this prints FAIL.  When OK is the symbol `m54-imp1-absent' itself the
file is absent, and this prints FAIL too.  Either way this registers a
real FAILING ERT test, so an absent src/ file is a real error, not a
pass."
  (let* ((absent (eq ok 'm54-imp1-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m54/imp1/%s (source file absent)\n" name))
      (princ (format "%s m54/imp1/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m54-imp1--registered (1+ m54-imp1--registered))
    (m54-imp1--bump-group)
    (imp-register-bool-as-ert-test (format "m54-imp1/%s" name) pass)))

;;; --- S2. The 3 stream fields and the boundary rule ------------------

;; The 3 FILE * streams of struct tty_display_info (brief.org section
;; 4.1).  Each check holds the field NAME, the FILE * TYPE, and the LINE
;; of the first match (brief.org section 6 prefers an ordered name list,
;; but the field line is stable state, so S2 pins it too).

(setq m54-imp1--group 's2)

(m54-imp1--check "termchar-input-field-51"
                 (and (m54-imp1--contains-p "src/termchar.h" "FILE *input;")
                      (eql 51 (m54-imp1--line-of "src/termchar.h"
                                                 "FILE \\*input;"))))
(m54-imp1--check "termchar-output-field-53"
                 (and (m54-imp1--contains-p "src/termchar.h" "FILE *output;")
                      (eql 53 (m54-imp1--line-of "src/termchar.h"
                                                 "FILE \\*output;"))))
(m54-imp1--check "termchar-termscript-field-61"
                 (and (m54-imp1--contains-p "src/termchar.h" "FILE *termscript;")
                      (eql 61 (m54-imp1--line-of "src/termchar.h"
                                                 "FILE \\*termscript;"))))
;; The boundary rule (brief.org section 4.4): a Guile port must NOT own a
;; C-owned FILE * stream; C stays the single writer.  The tracked source
;; holds the rule as a FIX marker on the M52 output boundary and in the
;; (emacs tty-output) module header.
(m54-imp1--check "boundary-rule-one-writer"
                 (and (m54-imp1--contains-p
                       "src/term.c"
                       "single writer of output / termscript; no Guile port owns a FILE *")
                      (m54-imp1--contains-p
                       "mod/emacs/tty-output.scm"
                       "C stays the single writer")))

;;; --- S3. The src/term.c site map ------------------------------------

;; brief.org section 4.2.  The ordered needle list holds one distinctive
;; string per stream operation, in file order: every output / termscript
;; write, every flush, the read handle, the open / close, the init, and
;; the size / baud queries.  A re-ordered or removed path breaks the
;; run.  A repeated identical form (for example the 6 routed
;; `m61_tty_handle_flush_1 (tty);' sites, or the 3 glyph-run calls)
;; appears once per occurrence, so the removal of one site is caught
;; too.

(setq m54-imp1--group 's3)

(m54-imp1--check "site-map-ordered-operations"
                 (m54-imp1--ordered-p
                  "src/term.c"
                  '(
                   ;; M61 imp-2: the 6 routed flush sites ask Scheme for
                   ;; the order decision, and the fflush itself stays C
                   ;; in the ONE mechanism m61_tty_output_flush_1.
                   "(void) m61_tty_handle_flush_1 (tty);"
                   "fwrite (SDATA (string), 1, SBYTES (string), tty->output);"
                   "fwrite (SDATA (string), 1, SBYTES (string), tty->termscript);"
                   "(void) m61_tty_handle_flush_1 (tty);"
                   "(void) m61_tty_handle_flush_1 (tty);"
                   "(void) m61_tty_handle_flush_1 (tty);"
                   "putc (' ', tty->termscript);"
                   "putc (' ', tty->output);"
                   ;; M61 imp-2: the 2 mechanisms of the ordered path (the
                   ;; termscript copy and the flush) and the ONE glyph-run
                   ;; entry point of the 3 hubs.  The hub call replaces the
                   ;; old write call plus its bare termscript fwrite.
                   "m61_tty_output_write_1 (struct tty_display_info *tty,"
                   "m61_tty_output_termscript_1 (struct tty_display_info *tty,"
                   "m61_tty_output_flush_1 (struct tty_display_info *tty)"
                   "m61_tty_handle_glyph_run_1 (tty, conversion_buffer,"
                   "m61_tty_handle_glyph_run_1 (tty, conversion_buffer,"
                   "m61_tty_handle_glyph_run_1 (tty, conversion_buffer,"
                   "f = t->display_info.tty->input;"
                   "emacs_fclose (t->display_info.tty->output);"
                   "(void) m61_tty_handle_flush_1 (tty);"
                   "(void) m61_tty_handle_flush_1 (tty);"
                   "tty->input = tty->output"
                   "add_keyboard_wait_descriptor (fileno (tty->input));"
                   "get_tty_size (fileno (tty->input), &width, &height);"
                   "init_baud_rate (fileno (tty->input));"
                   "tty->output = stdout;"
                   "tty->input = stdin;"
                   "get_tty_size (fileno (tty->input), &width, &height);"
                   ;; M54 imp-4 moved the tab policy to Scheme: the site
                   ;; is now the seam call, not the old C one-liner.
                   "m54_tty_tabs_verdict_scheme (tabs_safe ? Qt : Qnil,"
                   "init_baud_rate (fileno (tty->input));"
                   "delete_keyboard_wait_descriptor (fileno (tty->input));"
                   "emacs_fclose (tty->input);"
                   "emacs_fclose (tty->output);"
                   "emacs_fclose (tty->termscript);"
                   "m52_tty_write_1 (struct tty_display_info *tty"
                   "fwrite (str, 1, len, tty->output);"
                   "fwrite (str, 1, len, tty->termscript);"
                   "m52_tty_emit_cap_1 (struct tty_display_info *tty"
                   "fflush (tty->output)")))
;; The 4 --tty-* leaf DEFUNs (brief.org section 4.3).
(m54-imp1--check "leaf-defuns"
                 (m54-imp1--holds-all
                  "src/term.c"
                  '("DEFUN (\"--tty-emit-cap\""
                    "DEFUN (\"--tty-write-bytes\""
                    "DEFUN (\"--tty-flush\""
                    "DEFUN (\"--tty-emit-seq\"")))
;; The two M52 writer helpers (brief.org section 4.2).
(m54-imp1--check "writer-helpers"
                 (m54-imp1--holds-all
                  "src/term.c"
                  '("m52_tty_write_1 (struct tty_display_info *tty, const char *str"
                    "m52_tty_emit_cap_1 (struct tty_display_info *tty, Lisp_Object cap")))
;; The lifecycle anchors: init, read, write, flush, suspend, resume, and
;; close all live in these functions (brief.org section 4.2).
(m54-imp1--check "lifecycle-anchors"
                 (m54-imp1--holds-all
                  "src/term.c"
                  '("init_tty (const char *name"
                    "delete_tty (struct terminal *terminal)"
                    "get_tty_size (fileno (tty->input)"
                    "init_baud_rate (fileno (tty->input))"
                    "add_keyboard_wait_descriptor (fileno (tty->input))")))

;;; --- S4. The registration ------------------------------------------

(setq m54-imp1--group 's4)

(m54-imp1--check "run-tests-m54-imp1"
                 (m54-imp1--contains-p "tool/run-tests.scm"
                                       "test/m54/test-m54-imp1.el"))
(m54-imp1--check "run-tests-m54-group"
                 (m54-imp1--contains-p "tool/run-tests.scm" "(group (m54)"))
(m54-imp1--check "run-tests-m54-after-m53"
                 (m54-imp1--ordered-p "tool/run-tests.scm"
                                      '("(group (m53)" "(group (m54)")))
(m54-imp1--check "run-tests-m52-m53-present"
                 (and (m54-imp1--contains-p "tool/run-tests.scm" "(group (m52)")
                      (m54-imp1--contains-p "tool/run-tests.scm" "(group (m53)")))

;;; --- S5. The guards -------------------------------------------------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m54 gate proves nothing until the corpus exists and
;; its checks really register.  These guards fail when the corpus body
;; is truncated or its core checks do not run.  The counts are stable
;; because every check is registered at load time.  S2 holds 4 checks,
;; S3 holds 4, and S4 holds 4.  S1 is gone (M61 imp-2b, findings F2), so
;; it has no guard: a group that holds no check needs none.

(setq m54-imp1--group 's5)

(m54-imp1--check "reg/min-s2-checks-4" (>= (m54-imp1--group-count 's2) 4))
(m54-imp1--check "reg/min-s3-checks-4" (>= (m54-imp1--group-count 's3) 4))
(m54-imp1--check "reg/min-s4-checks-4" (>= (m54-imp1--group-count 's4) 4))

;;; --- The group-total check ------------------------------------------

;; The floor is the MEASURED count of m54-imp1 tests: 15 registered
;; checks (S2 4, S3 4, S4 4, S5 3) plus the group-total deftest itself.
;; This is a coarse net, not a tight bound; the per-group reg/min-*
;; guards are the tight check.  M61 imp-2b lowered this floor from 22
;; when findings F2 removed the 6 S1 source-text pins and the S1 guard.

(defvar m54-imp1--min-gate-total 16
  "The minimum number of m54-imp1 ERT tests: 15 registered checks plus
the group-total deftest, allowing one slack.")

(ert-deftest m54-imp1/gate-m54-total ()
  "The m54 group registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m54-imp" t))
              m54-imp1--min-gate-total)))

(princ (format "=== m54 imp-1 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d, s5 %d) ===\n"
               m54-imp1--registered
               (m54-imp1--group-count 's1)
               (m54-imp1--group-count 's2)
               (m54-imp1--group-count 's3)
               (m54-imp1--group-count 's4)
               (m54-imp1--group-count 's5)))
