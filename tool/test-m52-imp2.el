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
;;;         src/term.c 5,512 lines and 29 ^DEFUN lines (25 M48 DEFUNs
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
  "The group that `m52-imp2--check' counts into: `d7', `d8', or nil.")

(defvar m52-imp2--registered-d7 0
  "Number of D7 measured-surface checks registered.  D9 pins a minimum.")

(defvar m52-imp2--registered-d8 0
  "Number of D8 block-map checks registered.  D9 pins a minimum.")

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
             (setq m52-imp2--registered-d8 (1+ m52-imp2--registered-d8))))
      (imp-register-bool-as-ert-test (format "m52-imp2/%s" name) (and ok t)))))

;;; --- D7. The measured surface (docs/m52-plan.org section 8.2) --------

(setq m52-imp2--group 'd7)

(m52-imp2--check "term.c-lines-5512"
                 (eql 5512 (m52-imp2--lines "src/term.c")))
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
                 (eql 87 (m52-imp2--line-of "src/term.c" "#define OUTPUT(tty, a)")))
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

(princ (format "=== m52 imp-2 audit suite done (%d tracked checks: D7 %d, D8 %d) ===\n"
               m52-imp2--registered m52-imp2--registered-d7 m52-imp2--registered-d8))
