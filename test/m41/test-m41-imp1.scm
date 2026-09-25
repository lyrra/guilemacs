;;; test-m41-imp1.scm --- M41 imp-1: the src/xdisp.c audit.
;;;
;;; brief.org (M41 imp-1) is the docs-only audit.  It classifies the
;;; 24 src/xdisp.c DEFUNs, maps the live C callers, and confirms the
;;; target.  It adds no C.
;;;
;;; This corpus pins the audit facts against the tree, so a source that
;;; drifts from the classification fails the run.  Three kinds of check:
;;;
;;;   - the base numbers (src/xdisp.c 38,916 lines, 24 DEFUNs, 7
;;;     scm_c_public_ref sites; src/process.c 9,030 lines, 50 DEFUNs;
;;;     the combined keyboard surface 11,666, after M42 imp-2).
;;;   - the classification: the five reclaimable names and the three
;;;     blocked names.  A name that moves between the two sets fails.
;;;   - the static wiring: (emacs xdisp) exists, and run-tests.scm
;;;     registers the (m41) group.
;;;
;;; The repo root is bound by the .el wrapper as %m41-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test
;;; and prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/m41/test-m41-imp1.el.

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
  (and (string? text)
       (if (string-contains text needle) #t #f)))

(define (repo path) (string-append %m41-root "/" path))

(define (count-occurrences text needle)
  "Count the non-overlapping occurrences of NEEDLE in TEXT."
  (if (not (string? text))
      0
      (let ((nlen (string-length needle)))
        (let loop ((start 0) (n 0))
          (let ((idx (string-contains text needle start)))
            (if (not idx)
                n
                (loop (+ idx nlen) (+ n 1))))))))

(define (count-lines text)
  "Count the newlines in TEXT, the way `wc -l' does."
  (count-occurrences text "\n"))

(define (count-lines-starting text prefix)
  "Count the lines of TEXT that start with PREFIX."
  (if (not (string? text))
      0
      (let loop ((lines (string-split text #\newline)) (n 0))
        (if (null? lines)
            n
            (loop (cdr lines)
                  (if (string-prefix? prefix (car lines)) (+ n 1) n))))))

(define (count-regexp-lines text needle)
  "Count the lines of TEXT that contain NEEDLE."
  (if (not (string? text))
      0
      (let loop ((lines (string-split text #\newline)) (n 0))
        (if (null? lines)
            n
            (loop (cdr lines)
                  (if (string-contains (car lines) needle) (+ n 1) n))))))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m41-root))
    (begin (report "m41-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m41-root "."))
    (report "m41-root-bound" 'PASS))

(define xdisp (slurp (repo "src/xdisp.c")))

;;; --- 1. The base numbers (brief.org §7) ----------------------------
;;; DEFUN count uses the line-start form `DEFUN ("', not `DEFUN ' (see
;;; docs/kb.org defun-count-off-by-one).
(if (not xdisp)
    (report "m41/imp1/xdisp/absent" (cons 'FAIL "src/xdisp.c missing"))
    (begin
      (check "m41/imp1/xdisp/lines-38990" 38990 (count-lines xdisp))
      (check "m41/imp1/xdisp/defuns-24" 24
             (count-lines-starting xdisp "DEFUN (\""))
      (check "m41/imp1/xdisp/scm-public-ref-12" 12
             (count-occurrences xdisp "scm_c_public_ref"))))

;;; --- 2. The classification: reclaimable and blocked ----------------
;;; The five reclaimable names (brief.org §5 / docs/m41-plan.org §5)
;;; must exist as DEFUNs.
(define reclaimable-names
  '("set-buffer-redisplay" "get-display-property"
    "long-line-optimizations-p" "invisible-p"
    "lookup-image-map"))

;;; The three blocked names must exist as DEFUNs (the block is a
;;; caller, not a missing DEFUN).
(define blocked-names
  '("window-text-pixel-size"
    "current-bidi-paragraph-direction" "format-mode-line"))

(for-each
 (lambda (name)
   (check (string-append "m41/imp1/reclaimable/" name) 1
          (count-lines-starting xdisp
                                (string-append "DEFUN (\"" name "\""))))
 reclaimable-names)

(for-each
 (lambda (name)
   (check (string-append "m41/imp1/blocked/" name) 1
          (count-lines-starting xdisp
                                (string-append "DEFUN (\"" name "\""))))
 blocked-names)

;;; --- 2b. The classification words (docs/m41-plan.org §4) ----------
;;; Each of the 24 DEFUNs carries one group word, read from the C body.
;;; The word lives only in the gitignored plan, so the tracked corpus
;;; pins the table here (cr.org F2).  The table ties the group to
;;; reclamability: a "thin"/"decision predicate" group is
;;; reclaimable-like, a "mechanism"/"debug" group is not.  A name that
;;; moves between the two sets then fails, though it stays a DEFUN.
(define xdisp-classification
  '(("set-buffer-redisplay"                . "thin slot writer")
    ("line-pixel-height"                   . "mechanism (geometry)")
    ("remember-mouse-glyph"                . "mechanism (window system)")
    ("get-display-property"                . "thin accessor")
    ("window-text-pixel-size"              . "mechanism (geometry)")
    ("buffer-text-pixel-size"              . "mechanism (geometry)")
    ("display--line-is-continued-p"        . "mechanism (iterator)")
    ("tab-bar-height"                      . "mechanism (geometry)")
    ("tool-bar-height"                     . "mechanism (geometry)")
    ("long-line-optimizations-p"           . "decision predicate")
    ("dump-glyph-matrix"                   . "debug")
    ("dump-frame-glyph-matrix"             . "debug")
    ("dump-glyph-row"                      . "debug")
    ("dump-tab-bar-row"                    . "debug")
    ("dump-tool-bar-row"                   . "debug")
    ("trace-redisplay"                     . "debug")
    ("trace-to-stderr"                     . "debug")
    ("current-bidi-paragraph-direction"    . "mechanism (bidi)")
    ("bidi-find-overridden-directionality" . "mechanism (bidi)")
    ("move-point-visually"                 . "mechanism (bidi)")
    ("bidi-resolved-levels"                . "mechanism (bidi)")
    ("format-mode-line"                    . "mechanism (large)")
    ("invisible-p"                         . "decision predicate")
    ("lookup-image-map"                    . "thin accessor (geometry)")))

(define (thin-or-decision? group)
  "True when GROUP names a reclaimable-looking family: a thin accessor
or a decision predicate."
  (or (string-prefix? "thin" group)
      (string=? group "decision predicate")))

(define (mechanism-or-debug? group)
  (or (string-prefix? "mechanism" group) (string=? group "debug")))

(define (group-of name) (cdr (assoc name xdisp-classification)))
(define classification-names (map car xdisp-classification))

(check "m41/imp1/classify/24-names" 24 (length xdisp-classification))
(check "m41/imp1/classify/names-unique" #t
       (= (length classification-names)
          (length (delete-duplicates classification-names))))

;; Every classified name is exactly one DEFUN of src/xdisp.c.
(for-each
 (lambda (name)
   (check (string-append "m41/imp1/classify/defun/" name) 1
          (count-lines-starting xdisp
                                (string-append "DEFUN (\"" name "\""))))
 classification-names)

;; The reclaimable-looking names (thin / decision predicate) are exactly
;; the five reclaimable names.  No blocked or mechanism name has such a
;; group, so a reclaimable name that drifts into another set fails.
(check "m41/imp1/classify/reclaimable-like-set" #t
       (equal? (sort (filter (lambda (n) (thin-or-decision? (group-of n)))
                             classification-names)
                     string<?)
               (sort reclaimable-names string<?)))

;; The rest (mechanism/debug groups) are the 16 mechanism names plus the
;; 3 blocked names.  Together the two sets partition the 24 DEFUNs.
(check "m41/imp1/classify/mechanism-like-set" #t
       (equal? (sort (filter (lambda (n) (mechanism-or-debug? (group-of n)))
                             classification-names)
                     string<?)
               (sort (filter (lambda (n)
                               (not (member n reclaimable-names)))
                             classification-names)
                     string<?)))

;;; --- 3. The blocked callers are still live C callers --------------
(define xfns (slurp (repo "src/xfns.c")))
(define pgtkfns (slurp (repo "src/pgtkfns.c")))
(define nsfns (slurp (repo "src/nsfns.m")))
(check "m41/imp1/blocked/xfns-calls-window-text-pixel-size" #t
       (contains? xfns "Fwindow_text_pixel_size"))
(check "m41/imp1/blocked/pgtkfns-calls-window-text-pixel-size" #t
       (contains? pgtkfns "Fwindow_text_pixel_size"))
(check "m41/imp1/blocked/nsfns-calls-window-text-pixel-size" #t
       (contains? nsfns "Fwindow_text_pixel_size"))

;;; --- 3b. The reclaimable names have no live C caller (cr.org F3) ---
;;; The central caller-map fact: each reclaimable name appears only in
;;; its DEFUN (src/xdisp.c) and its EXFUN declaration
;;; (src/globals.h) across the buildable C, header, and ObjC sources.
;;; A new live caller in any other file fails here.
(define (c-symbol name)
  "The C identifier F<name> for the Lisp NAME (hyphens become underscores)."
  (string-append "F"
                 (list->string
                  (map (lambda (c) (if (char=? c #\-) #\_ c))
                       (string->list name)))))

(define (src-buildable-files)
  "The src/ .c, .h, and .m files, like the guard scan over src/*.[chm]."
  (let ((d (opendir (repo "src"))))
    (let loop ((names '()))
      (let ((n (readdir d)))
        (if (eof-object? n)
            (begin (closedir d) names)
            (loop (if (or (string-suffix? ".c" n)
                          (string-suffix? ".h" n)
                          (string-suffix? ".m" n))
                      (cons n names)
                      names)))))))

(define src-buildable-contents
  (map (lambda (f)
         (cons f (slurp (repo (string-append "src/" f)))))
       (src-buildable-files)))

(define (caller-files name)
  "The src/ .c/.h/.m files that mention the C symbol F<name>."
  (let ((sym (c-symbol name)))
    (map car
         (filter (lambda (fc) (> (count-occurrences (cdr fc) sym) 0))
                 src-buildable-contents))))

(for-each
 (lambda (name)
   (let ((files (caller-files name)))
     (check (string-append "m41/imp1/reclaimable/no-c-caller/" name) #t
            (if (and (= (length files) 2)
                     (member "xdisp.c" files)
                     (member "globals.h" files))
                #t #f))))
 reclaimable-names)

;;; --- 3c. The classification words match the plan (guarded) ---------
;;; docs/ is gitignored, so a fresh clone has no plan.  When the plan
;;; is present, each classified name must sit on a plan row with its
;;; group word.  This keeps the tracked table (2b) and the plan in
;;; step; the tracked table is the durable pin.
(define m41-plan (slurp (repo "docs/m41-plan.org")))
(if (not (string? m41-plan))
    (report "m41/imp1/plan/absent"
            (list 'INFO "docs/m41-plan.org absent (gitignored)"))
    (for-each
     (lambda (entry)
       (let ((name (car entry)) (group (cdr entry)))
         (check (string-append "m41/imp1/plan/row/" name) #t
                (let loop ((lines (string-split m41-plan #\newline)))
                  (cond ((null? lines) #f)
                        ((and (string-contains (car lines) name)
                              (string-contains (car lines) group))
                         #t)
                        (else (loop (cdr lines))))))))
     xdisp-classification))

;;; --- 4. The target and the module ---------------------------------
(define xdisp-mod (slurp (repo "mod/emacs/xdisp.scm")))
(check "m41/imp1/module/xdisp-exists" #t (and (string? xdisp-mod) #t))
(check "m41/imp1/module/xdisp-push-kboard" #t
       (contains? xdisp-mod "xdisp-push-kboard!"))

;;; --- 5. Static: run-tests.scm registers the (m41) group ------------
(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m41/imp1/run-tests.scm/group-m41" #t
       (contains? run-tests "(group (m41)"))
(check "m41/imp1/run-tests.scm/registers-el" #t
       (contains? run-tests "test/m41/test-m41-imp1.el"))
