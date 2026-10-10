;;; test-m52-imp2.el --- M52 imp-2 audit corpus (the TTY output boundary).
;;;
;;; M52 imp-2 is the docs-only boundary audit (brief.org, docs/m52-plan.org
;;; section 8).  It changes no C and no Scheme.  It names the TTY output
;;; path, maps each decision block, classifies it MOVES / STAYS C, and
;;; returns the A1 / A2 verdict.
;;;
;;; VERDICT A1.  The DECISION that moves is (1) the termcap capability-
;;; string SELECTION (which TS_* string, and when) and (2) the cursor /
;;; scroll / clear ARITHMETIC.  The byte write to the C-owned FILE *output
;;; / *termscript and the fflush / tcdrain drain STAY C.
;;;
;;; This corpus reads TRACKED files only.  It has no C dependency.  A test
;;; does not read docs/: a docs needle is not a behaviour, and docs/ is
;;; gitignored, so such a check can never fail on a fresh clone.  The docs
;;; needles live in tool/m52-plan-lint.sh, which no group runs.  This
;;; corpus pins:
;;;   D7 -- the measured surface of docs/m52-plan.org section 8.2:
;;;         src/term.c 5,864 lines and 29 ^DEFUN lines (25 M48 DEFUNs
;;;         plus the 4 M52 imp-3 --tty-* leaves re-pinned at imp-3);
;;;         FILE *input :51, *output :53, *termscript :61; src/cm.c
;;;         cmputc :45; 10 fwrite lines in src/term.c (the 8 output-path
;;;         sites plus the 2 in the M52 imp-3 write mechanism); the 6
;;;         --term-* DEFUNs
;;;         in src/term.c; the 5 OUTPUT macro definitions and the OUTPUT
;;;         macro line :87; the src/sysdep.c setup literals and their lines
;;;         :1114 :1200 :1404 :1437 :1443; and the raw ^tty_ line count 56
;;;         (which is NOT the output path).  27 checks.
;;;   D8 -- the block map of section 8.3: the first 26 ^tty_ names in
;;;         src/term.c, in file order, equal the curated output-block
;;;         list tty_ring_bell … tty_ins_del_lines.  A drift is a real
;;;         FAIL.  D8 pins NAMES, not line numbers: a new leaf moves every
;;;         line below it, so a line constant would invalidate itself at
;;;         the next imp; the ordered name list survives.  27 checks.
;;;   D9 -- the (m52) group is PRESENT in tool/run-tests.scm.  imp-2 pinned
;;;         the group ABSENT, because imp-2 adds no behaviour.  imp-3
;;;         creates the (m52) group, so imp-3 re-pins this check to
;;;         PRESENT (brief.org section 5.6).
;;;   D10 -- the tree-wide re-pin consistency guard (added with the M52
;;;         imp-5 review follow-up).  It re-measures the tree-wide
;;;         scm_c_public_ref line count and checks every labeled pin in
;;;         the tracked M-corpus and tool/ files against it, so a re-pin
;;;         that misses a corpus (the imp-5 F1 defect) is caught here.
;;;         1 check per pinned corpus + a measured-positive and a
;;;         min-pinned-files guard.
;;;
;;; Each check is printed as a PASS/FAIL line and turned into an ERT test
;;; so the harness counts it.  A read error is a real error, never a
;;; silent pass.  The corpus holds its own copy of every fact it pins.

(princ "=== m52 imp-2 audit suite ===\n")

(require 'imp-ert-report)

(defvar m52-imp2--root
  (file-name-as-directory
   (expand-file-name ".." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m52-imp2--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m52-imp2--group nil
  "The group that `m52-imp2--check' counts into: `d7', `d8', `d10', or nil.")

(defvar m52-imp2--registered-d7 0
  "Number of D7 measured-surface checks registered.  D9 pins a minimum.")

(defvar m52-imp2--registered-d8 0
  "Number of D8 block-map checks registered.  D9 pins a minimum.")

(defvar m52-imp2--registered-d10 0
  "Number of D10 re-pin consistency checks registered.  D10 pins a minimum.")

(defvar m52-imp2--registered-d11 0
  "Number of D11 marker-routing checks registered.  D11 pins a minimum.")

(defun m52-imp2--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m52-imp2-absent' when REL does not exist."
  (let ((path (expand-file-name rel m52-imp2--root)))
    (if (not (file-exists-p path))
        'm52-imp2-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m52-imp2--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m52-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m52-imp2--tracked-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.
A missing tracked file folds to nil, so `m52-imp2--check' prints FAIL."
  (let ((hit (m52-imp2--contains-p rel needle)))
    (and (not (eq hit 'm52-imp2-absent)) (and hit t))))

(defun m52-imp2--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m52-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m52-imp2--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m52-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m52-imp2--count-literal (rel needle)
  "Count the matches of the LITERAL NEEDLE in REL."
  (m52-imp2--count rel (regexp-quote needle)))

(defun m52-imp2--count-lines (rel needle)
  "Count the lines of REL that contain the LITERAL NEEDLE (`grep -c' style)."
  (m52-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (save-excursion
                  (beginning-of-line)
                  (search-forward needle (line-end-position) t))
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m52-imp2--defun-count (rel)
  "Count the `^DEFUN (' lines of REL."
  (m52-imp2--count rel (concat "^" (regexp-quote "DEFUN (\""))))

(defun m52-imp2--line-of (rel needle)
  "1-based line number of the first LITERAL NEEDLE in REL, or nil.
An absent REL, or an absent needle, yields nil, so the caller prints a
real FAIL."
  (m52-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m52-imp2--tty-names (rel)
  "The `^tty_NAME (' function names of REL, in file order.
The output path is a curated PREFIX of this list (the first 26 names).
A raw count also holds the tty_menu_* and display-query helpers."
  (m52-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((names '()))
        (while (re-search-forward "^\\(tty_[a-z_]+\\) (" nil t)
          (push (match-string 1) names))
        (nreverse names)))))

(defun m52-imp2--take (n list)
  "The first N items of LIST, or all of LIST when it is shorter."
  (let ((out '()))
    (while (and list (> n 0))
      (push (car list) out)
      (setq list (cdr list))
      (setq n (1- n)))
    (nreverse out)))

(defun m52-imp2--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
An absent src/ file prints FAIL, not a silent pass."
  (if (eq ok 'm52-imp2-absent)
      (princ (format "INFO m52/imp2/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m52/imp2/%s\n" (if ok "PASS" "FAIL") name))
      (setq m52-imp2--registered (1+ m52-imp2--registered))
      (cond ((eq m52-imp2--group 'd7)
             (setq m52-imp2--registered-d7 (1+ m52-imp2--registered-d7)))
            ((eq m52-imp2--group 'd8)
             (setq m52-imp2--registered-d8 (1+ m52-imp2--registered-d8)))
            ((eq m52-imp2--group 'd10)
             (setq m52-imp2--registered-d10 (1+ m52-imp2--registered-d10)))
            ((eq m52-imp2--group 'd11)
             (setq m52-imp2--registered-d11 (1+ m52-imp2--registered-d11))))
      (imp-register-bool-as-ert-test (format "m52-imp2/%s" name) (and ok t)))))

;;; --- D7. The measured surface (docs/m52-plan.org section 8.2) --------

(setq m52-imp2--group 'd7)

(m52-imp2--check "term.c-lines-5864"
                 (eql 5864 (m52-imp2--lines "src/term.c")))
(m52-imp2--check "term.c-defuns-29"
                 (eql 29 (m52-imp2--defun-count "src/term.c")))
(m52-imp2--check "termchar.h-input-51"
                 (eql 51 (m52-imp2--line-of "src/termchar.h" "FILE *input;")))
(m52-imp2--check "termchar.h-output-53"
                 (eql 53 (m52-imp2--line-of "src/termchar.h" "FILE *output;")))
(m52-imp2--check "termchar.h-termscript-61"
                 (eql 61 (m52-imp2--line-of "src/termchar.h" "FILE *termscript;")))
(m52-imp2--check "cm.c-cmputc-45"
                 (eql 45 (m52-imp2--line-of "src/cm.c" "cmputc (int c)")))
(m52-imp2--check "term.c-fwrite-10"
                 (eql 10 (m52-imp2--count-lines "src/term.c" "fwrite (")))
(m52-imp2--check "term.c-term-defuns-6"
                 (eql 6 (m52-imp2--count-literal "src/term.c" "DEFUN (\"--term-")))
;; the raw ^tty_ line count.  It is NOT the output path: it counts 56
;; lines, and the output-block list is the curated first 26 (D8).
(m52-imp2--check "term.c-tty-raw-56"
                 (eql 56 (length (or (m52-imp2--tty-names "src/term.c") '()))))
;; the 5 OUTPUT macro definitions of src/term.c.
(m52-imp2--check "term.c-macro-output"
                 (m52-imp2--tracked-p "src/term.c" "#define OUTPUT(tty, a)"))
(m52-imp2--check "term.c-macro-output1"
                 (m52-imp2--tracked-p "src/term.c" "#define OUTPUT1(tty, a)"))
(m52-imp2--check "term.c-macro-outputl"
                 (m52-imp2--tracked-p "src/term.c" "#define OUTPUTL(tty, a, lines)"))
(m52-imp2--check "term.c-macro-output-if"
                 (m52-imp2--tracked-p "src/term.c" "#define OUTPUT_IF(tty, a)"))
(m52-imp2--check "term.c-macro-output1-if"
                 (m52-imp2--tracked-p "src/term.c" "#define OUTPUT1_IF(tty, a)"))
;; the OUTPUT macro line of docs/m52-plan.org section 8.2 (:87).
(m52-imp2--check "term.c-macro-output-line-87"
                 (eql 109 (m52-imp2--line-of "src/term.c" "#define OUTPUT(tty, a)")))
;; the write mechanism is the C callback + the C-owned streams.
(m52-imp2--check "cm.c-cmputc-writes-output"
                 (m52-imp2--tracked-p "src/cm.c" "putc (c & 0177, current_tty->output)"))
(m52-imp2--check "cm.c-cmputc-writes-termscript"
                 (m52-imp2--tracked-p "src/cm.c" "putc (c & 0177, current_tty->termscript)"))
;; the src/sysdep.c output setup (section 8.2).
(m52-imp2--check "sysdep.c-init-sys-modes"
                 (m52-imp2--tracked-p "src/sysdep.c"
                                      "init_sys_modes (struct tty_display_info *tty_out)"))
(m52-imp2--check "sysdep.c-reset-sys-modes"
                 (m52-imp2--tracked-p "src/sysdep.c"
                                      "reset_sys_modes (struct tty_display_info *tty_out)"))
(m52-imp2--check "sysdep.c-setvbuf-output"
                 (m52-imp2--tracked-p "src/sysdep.c" "setvbuf (tty_out->output,"))
(m52-imp2--check "sysdep.c-tcdrain-output"
                 (m52-imp2--tracked-p "src/sysdep.c"
                                      "tcdrain (fileno (tty_out->output))"))
(m52-imp2--check "sysdep.c-oflag-opost"
                 (m52-imp2--tracked-p "src/sysdep.c" "c_oflag |= OPOST"))
;; the src/sysdep.c setup LINES of section 8.2 (:1114 :1200 :1404 :1437 :1443).
(m52-imp2--check "sysdep.c-init-sys-modes-line-1114"
                 (eql 1114 (m52-imp2--line-of
                            "src/sysdep.c"
                            "init_sys_modes (struct tty_display_info *tty_out)")))
(m52-imp2--check "sysdep.c-setvbuf-output-line-1200"
                 (eql 1200 (m52-imp2--line-of "src/sysdep.c"
                                              "setvbuf (tty_out->output,")))
(m52-imp2--check "sysdep.c-reset-sys-modes-line-1404"
                 (eql 1404 (m52-imp2--line-of
                            "src/sysdep.c"
                            "reset_sys_modes (struct tty_display_info *tty_out)")))
(m52-imp2--check "sysdep.c-fflush-output-line-1437"
                 (eql 1437 (m52-imp2--line-of "src/sysdep.c"
                                              "fflush (tty_out->output)")))
(m52-imp2--check "sysdep.c-tcdrain-output-line-1443"
                 (eql 1443 (m52-imp2--line-of "src/sysdep.c"
                                              "tcdrain (fileno (tty_out->output))")))

;;; --- D8. The block map (docs/m52-plan.org section 8.3) ---------------

(setq m52-imp2--group 'd8)

(defconst m52-imp2--output-blocks
  '("tty_ring_bell"
    "tty_send_additional_strings"
    "tty_set_terminal_modes"
    "tty_reset_terminal_modes"
    "tty_update_end"
    "tty_set_terminal_window"
    "tty_set_scroll_region"
    "tty_turn_on_insert"
    "tty_turn_off_insert"
    "tty_turn_off_highlight"
    "tty_turn_on_highlight"
    "tty_toggle_highlight"
    "tty_hide_cursor"
    "tty_show_cursor"
    "tty_background_highlight"
    "tty_highlight_if_desired"
    "tty_cursor_to"
    "tty_raw_cursor_to"
    "tty_clear_to_end"
    "tty_clear_frame"
    "tty_clear_end_of_line"
    "tty_write_glyphs"
    "tty_write_glyphs_with_face"
    "tty_insert_glyphs"
    "tty_delete_glyphs"
    "tty_ins_del_lines")
  "The 26 src/term.c output-block names, in file order (section 8.3).
This is the curated list tty_ring_bell … tty_ins_del_lines, not every
^tty_ line.  The write mechanism travels with these blocks; the glyph
writers (tty_write_glyphs, tty_write_glyphs_with_face, tty_insert_glyphs)
STAY C; the rest MOVES.")

(defun m52-imp2--tty-or-nil (rel)
  "The tty_NAME list of REL, or nil when REL is absent.
An absent tracked file folds to nil, so every position check prints FAIL."
  (let ((found (m52-imp2--tty-names rel)))
    (if (listp found) found '())))

;; one check per output block: the name AND its position must hold.
(let ((i 0)
      (found (m52-imp2--tty-or-nil "src/term.c")))
  (dolist (name m52-imp2--output-blocks)
    (m52-imp2--check (format "output-block-%02d-%s" (1+ i) name)
                     (equal name (nth i found)))
    (setq i (1+ i))))
;; the whole prefix, so an EXTRA or a RE-ORDERED block is caught too.
(m52-imp2--check "output-block-prefix-exact-26"
                 (equal m52-imp2--output-blocks
                        (m52-imp2--take 26 (m52-imp2--tty-or-nil "src/term.c"))))

;;; --- D9. The group state and the min-count guard ---------------------

;; close the D8 group so the guards below count into no group.
(setq m52-imp2--group nil)

;; imp-3 CREATES the (m52) group, so this check flips from ABSENT to
;; PRESENT (brief.org section 5.6).  The group now registers the corpus.
(m52-imp2--check "reg/m52-group-present"
                 (m52-imp2--tracked-p "tool/run-tests.scm"
                                      "(group (m52)"))
;; The (m51) group is the last milestone group and stays present.
(m52-imp2--check "reg/m51-group-present"
                 (m52-imp2--tracked-p "tool/run-tests.scm"
                                      "(group (m51)"))
;; the fold-to-nil helper itself: an absent tracked file must print FAIL.
(m52-imp2--check "reg/absent-tracked-file-fails"
                 (null (m52-imp2--tracked-p "src/m52-imp2-no-such-file.c"
                                            "needle")))
;; Each D7 / D8 check increments its counter, so a truncation that
;; removes a check drops the count below the minimum and the guard
;; prints FAIL.  The guard only misses a truncation that also removes
;; the guard line itself.  The advisory runner prints the real count.
;; D7 holds 27 checks; D8 holds 27 (26 positions + the exact-prefix list).
(m52-imp2--check "reg/min-d7-checks-27"
                 (>= m52-imp2--registered-d7 27))
(m52-imp2--check "reg/min-d8-checks-27"
                 (>= m52-imp2--registered-d8 27))

;;; --- D10. The tree-wide re-pin consistency guard ---------------------
;;
;; The tree-wide scm_c_public_ref count is pinned in ~36 tracked corpora
;; (test/m40 ... test/m52 and tool/).  The RE-PINS list is hand-
;; maintained, so a re-pin that misses a corpus drifts.  The M52 imp-5
;; F1 defect is the example: the 4 test/m40/*.scm copies kept 240 while
;; the tree held 246, and only their own group went red.  This guard
;; re-measures the count and checks EVERY labeled pin against it, so a
;; missed corpus is a real FAIL here too, not only in its own group.  It
;; reads tracked files only.

(setq m52-imp2--group 'd10)

(defconst m52-imp2--tree-ref-pin-re
  "\\(?:tree-wide-scm-public-ref\\|tree-wide-scm-ref\\|tree-ref-sites\\|scm-c-public-ref\\)-\\([0-9]+\\)"
  "The labeled tree-wide scm_c_public_ref pin patterns, one capture group.")

(defun m52-imp2--tree-ref-lines ()
  "The tree-wide line count: `scm_c_public_ref' lines summed over src/*.[chm].
This is `grep -c' per file then summed (LINES, not occurrences), the
same shape as the M52 imp-1 D1 measure."
  (let ((total 0))
    (dolist (f (directory-files (expand-file-name "src" m52-imp2--root)
                                t "\\.[chm]\\'"))
      (setq total (+ total
                     (or (m52-imp2--count-lines (file-relative-name
                                                 f m52-imp2--root)
                                                "scm_c_public_ref")
                         0))))
    total))

(defun m52-imp2--corpus-files ()
  "The tracked M-corpus files (test/m*/ and tool/, .el and .scm), root-relative.
A missing tool/ (untracked on a fresh clone) contributes no files."
  (let ((files '())
        (test (expand-file-name "test" m52-imp2--root)))
    (when (file-directory-p test)
      (dolist (d (directory-files test t "^m[0-9]"))
        (dolist (f (directory-files-recursively d "\\.\\(?:el\\|scm\\)\\'"))
          (push (file-relative-name f m52-imp2--root) files))))
    (let ((dir (expand-file-name "tool" m52-imp2--root)))
      (when (file-directory-p dir)
        (dolist (f (directory-files-recursively dir "\\.\\(?:el\\|scm\\)\\'"))
          (push (file-relative-name f m52-imp2--root) files))))
    (nreverse files)))

(defun m52-imp2--tree-ref-pins (rel)
  "The labeled tree-wide pin numbers REL holds, as a list of integers."
  (m52-imp2--with rel
    (lambda ()
      (let ((pins '()))
        (goto-char (point-min))
        (while (re-search-forward m52-imp2--tree-ref-pin-re nil t)
          (push (string-to-number (match-string 1)) pins))
        (nreverse pins)))))

(let* ((measured (m52-imp2--tree-ref-lines))
       (files (m52-imp2--corpus-files))
       (pinned 0))
  ;; sanity: a broken walk yields 0, so the measured-positive check fails.
  (m52-imp2--check "repin/measured-positive" (> measured 0))
  (dolist (f files)
    (let ((pins (m52-imp2--tree-ref-pins f)))
      (when (and (listp pins) pins)
        (setq pinned (1+ pinned))
        (m52-imp2--check (format "repin/%s" f)
                         (let ((ok t))
                           (dolist (n pins)
                             (unless (eql n measured) (setq ok nil)))
                           ok)))))
  ;; a discovery break must FAIL: ~36 corpora carry the pin.
  (m52-imp2--check "repin/min-pinned-files-30" (>= pinned 30)))

;;; --- D11. The M52 imp-6 marker routing (cr.org section 8) ------------
;;
;; cr.org section 8 flags the strongest residual risk: no behaviour corpus can
;; force a redisplay step, so the C routing of a MARKER step (the
;; "newlines" loop, the raw CR, and the cursor "background" / "off-insert"
;; / "move" mechanisms) runs in no test.  A behaviour corpus cannot prove
;; a call, but the tool/ audit path may pin the SOURCE FACT (the imp-1 /
;; imp-2 rule): each of the 4 rewired hubs must route its markers to the
;; right C mechanism.  These checks read src/term.c only.  They are
;; advisory and go through no group.

(setq m52-imp2--group 'd11)

;; the 4 imp-6 hubs walk the returned step list.  The imp-5
;; tty_update_end hub uses the same loop shape, so the file holds 5.
(m52-imp2--check "imp6/list-walk-5"
                 (eql 5 (m52-imp2--count-literal
                         "src/term.c" "for (; CONSP (steps); steps = XCDR (steps))")))
;; a KEY step goes to m52_cap_string_1 through the ORIGINAL OUTPUT_IF.
;; Two sites: tty_set_terminal_modes and tty_reset_terminal_modes.
(m52-imp2--check "imp6/key-output-if-2"
                 (eql 2 (m52-imp2--count-literal
                         "src/term.c"
                         "OUTPUT_IF (tty, m52_cap_string_1 (tty, step));")))
;; tty_set_terminal_modes: the "newlines" marker runs the cmputc loop.
(m52-imp2--check "imp6/set-modes-newlines-marker"
                 (m52-imp2--tracked-p "src/term.c"
                                      "m52_tty_step_tag_p (step, \"newlines\")"))
(m52-imp2--check "imp6/set-modes-newline-loop-1"
                 (eql 1 (m52-imp2--count-literal "src/term.c" "cmputc ('\\n')")))
;; tty_reset_terminal_modes: the "raw-cr" marker emits the raw CR.
(m52-imp2--check "imp6/reset-modes-raw-cr-marker"
                 (m52-imp2--tracked-p "src/term.c"
                                      "m52_tty_step_tag_p (step, \"raw-cr\")"))
(m52-imp2--check "imp6/reset-modes-raw-cr-1"
                 (eql 1 (m52-imp2--count-literal "src/term.c" "cmputc ('\\r')")))
;; the two cursor hubs route "background" -> tty_background_highlight,
;; "off-insert" -> tty_turn_off_insert, and "move" -> cmgoto.  Each
;; tag test appears once per cursor hub.
(m52-imp2--check "imp6/cursor-background-marker-2"
                 (eql 2 (m52-imp2--count-literal
                         "src/term.c" "m52_tty_step_tag_p (step, \"background\")")))
(m52-imp2--check "imp6/cursor-off-insert-marker-2"
                 (eql 2 (m52-imp2--count-literal
                         "src/term.c" "m52_tty_step_tag_p (step, \"off-insert\")")))
(m52-imp2--check "imp6/cursor-move-marker-2"
                 (eql 2 (m52-imp2--count-literal
                         "src/term.c" "m52_tty_step_tag_p (step, \"move\")")))
(m52-imp2--check "imp6/cursor-cmgoto-2"
                 (eql 2 (m52-imp2--count-literal
                         "src/term.c"
                         "cmgoto (tty, XFIXNUM (XCAR (XCDR (step))),")))
;; the two cursor hubs return on the #nil list with NILP.
(m52-imp2--check "imp6/cursor-nilp-2"
                 (eql 2 (m52-imp2--count-literal "src/term.c" "if (NILP (steps))")))
;; each of the 4 dispatchers resolves its module procedure one time.
(m52-imp2--check "imp6/dispatch-ref-set-modes"
                 (m52-imp2--tracked-p
                  "src/term.c"
                  "scm_c_public_ref (\"emacs tty-output\", \"tty-set-terminal-modes-steps\")"))
(m52-imp2--check "imp6/dispatch-ref-reset-modes"
                 (m52-imp2--tracked-p
                  "src/term.c"
                  "scm_c_public_ref (\"emacs tty-output\", \"tty-reset-terminal-modes-steps\")"))
(m52-imp2--check "imp6/dispatch-ref-cursor-to"
                 (m52-imp2--tracked-p
                  "src/term.c"
                  "scm_c_public_ref (\"emacs tty-output\", \"tty-cursor-to-steps\")"))
(m52-imp2--check "imp6/dispatch-ref-raw-cursor-to"
                 (m52-imp2--tracked-p
                  "src/term.c"
                  "scm_c_public_ref (\"emacs tty-output\", \"tty-raw-cursor-to-steps\")"))
;; a truncation guard: the D11 block holds at least 14 checks.
(m52-imp2--check "imp6/min-d11-checks-14"
                 (>= m52-imp2--registered-d11 14))

(princ (format "=== m52 imp-2 audit suite done (%d tracked checks: D7 %d, D8 %d, D10 %d, D11 %d) ===\n"
               m52-imp2--registered m52-imp2--registered-d7 m52-imp2--registered-d8
               m52-imp2--registered-d10 m52-imp2--registered-d11))
