;;; test-m49-imp3.el --- M49 imp-3 corpus (the G1 listing policy in Scheme).
;;;
;;; M49 imp-3 moves the G1 listing policy of src/dired.c into
;;; (emacs dired) (brief.org section 7).  The G1 decision -- the
;;; separator, the full join, the match, the count, and the sort key --
;;; now runs in Scheme.  C keeps the mechanism: the readdir loop and the
;;; unwind guard in the static helper dired_read_names_1.
;;;
;;; This corpus reads TRACKED files only (brief.org section 8).  It pins:
;;;   F1 -- the deleted leaf: `--dired-listing-names' and
;;;         `Fdired_listing_names' are absent from src/dired.c; the new
;;;         static helper dired_read_names_1 is present and holds the
;;;         mechanism (read_dirent, open_directory, scm_from_utf8_stringn)
;;;         and NO hub and NO policy; the hub `directory-files' calls the
;;;         raw reader and the Scheme policy; the ^DEFUN count is 11 and
;;;         the ref count is 1.
;;;   F2 -- the Scheme policy: mod/emacs/dired.scm holds the separator,
;;;         the full join, `string-match-p', the count, and
;;;         `string-lessp'; 3 --dired-* defelisp leaves remain; no FFI and
;;;         no scm_c_public_ref.
;;;   F3 -- runtime probes of `directory-files' over temp directories
;;;         with FULL, MATCH, NOSORT, and COUNT (brief.org section 8).
;;;         These exercise the moved decision in Scheme.  Note that
;;;         `directory-files' lists "." and ".." too, so the MATCH probes
;;;         pin a deterministic subset.  One probe also pins that the
;;;         policy keeps the match data (the D1 fix, cr.org 5.1).
;;;   F5 -- the (m49) group carries this corpus, and a per-group
;;;         min-count guard fails when the corpus is truncated.
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real error.  This corpus reads no docs/ needle
;;; (docs/kb.org test-must-not-read-docs).  The probe error is a FAIL,
;;; never a silent pass (docs/kb.org
;;; m4x-probe-failure-must-not-read-as-a-skip).

(princ "=== m49 imp-3 listing-policy suite ===\n")

(require 'imp-ert-report)

(defvar m49-imp3--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m49-imp3--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m49-imp3--group nil
  "The group that `m49-imp3--check' counts into: `f1' ... `f3', or nil.")

(defvar m49-imp3--counts nil
  "Alist of (GROUP . COUNT) for the registered tracked-file checks.")

(defun m49-imp3--group-count (group)
  "Number of tracked-file checks registered so far in GROUP."
  (or (cdr (assq group m49-imp3--counts)) 0))

(defun m49-imp3--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m49-imp3-absent' when REL does not exist."
  (let ((path (expand-file-name rel m49-imp3--root)))
    (if (not (file-exists-p path))
        'm49-imp3-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m49-imp3--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m49-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m49-imp3--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m49-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m49-imp3--count-code (rel regexp)
  "Count the matches of REGEXP in REL, skipping full comment lines.
A module comment may name a forbidden token while explaining the
contract; only the code must be free of the token.  Scheme line comments
start with `;'."
  (m49-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (let ((line (buffer-substring-no-properties
                       (line-beginning-position) (line-end-position))))
            (unless (string-match-p "^[ \t]*;" line)
              (save-excursion
                (end-of-line)
                (let ((eol (point)))
                  (beginning-of-line)
                  (while (re-search-forward regexp eol t)
                    (setq n (1+ n)))))))
          (forward-line 1))
        n))))

(defun m49-imp3--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
An absent src/ file makes the reader return the symbol
`m49-imp3-absent', so the check prints FAIL -- an absent src/ file is a
real error, not a pass."
  (if (eq ok 'm49-imp3-absent)
      (princ (format "INFO m49/imp3/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m49/imp3/%s\n" (if ok "PASS" "FAIL") name))
      (setq m49-imp3--registered (1+ m49-imp3--registered))
      (when m49-imp3--group
        (let ((cell (assq m49-imp3--group m49-imp3--counts)))
          (if cell
              (setcdr cell (1+ (cdr cell)))
            (push (cons m49-imp3--group 1) m49-imp3--counts))))
      (imp-register-bool-as-ert-test (format "m49-imp3/%s" name) (and ok t)))))

(defun m49-imp3--fn-body (name)
  "Return the C source of the function NAME in src/dired.c, from the
line before its name (the return-type line, so `static' is included) to
the closing `\\n}' at column 0, or nil."
  (m49-imp3--with "src/dired.c"
    (lambda ()
      (goto-char (point-min))
      (when (search-forward (concat "\n" name " (") nil t)
        (let ((start (save-excursion (forward-line -1) (line-beginning-position))))
          (if (search-forward "\n}" nil t)
              (buffer-substring-no-properties start (match-end 0))
            (buffer-substring-no-properties start (point-max))))))))

;;; --- F1. The C surface (brief.org section 7.1 and section 7.3) ------

(setq m49-imp3--group 'f1)

;; The deleted leaf: no token of it may remain (brief.org section 7.3).
(m49-imp3--check "leaf-token-absent"
                 (not (m49-imp3--contains-p "src/dired.c"
                                            "--dired-listing-names")))
(m49-imp3--check "leaf-fname-token-absent"
                 (not (m49-imp3--contains-p "src/dired.c"
                                            "Fdired_listing_names")))

;; The new static helper (brief.org section 7.1).
(m49-imp3--check "helper-present"
                 (m49-imp3--contains-p "src/dired.c"
                                       "dired_read_names_1 (Lisp_Object directory)"))
(let ((body (m49-imp3--fn-body "dired_read_names_1")))
  (m49-imp3--check "helper-is-static"
                   (and (stringp body)
                        (string-match-p "static Lisp_Object" body) t))
  (m49-imp3--check "helper-mech-readdir"
                   (and (stringp body) (string-match-p "read_dirent" body) t))
  (m49-imp3--check "helper-mech-open"
                   (and (stringp body) (string-match-p "open_directory" body) t))
  (m49-imp3--check "helper-mech-string"
                   (and (stringp body)
                        (string-match-p "scm_from_utf8_stringn" body) t))
  ;; The helper calls the mechanism, not a hub (leaf-must-call-the-
  ;; mechanism).  It uses directory_files_internal_unwind, so the check
  ;; looks for a CALL with the open paren.
  (m49-imp3--check "helper-no-hub"
                   (and (stringp body)
                        (not (string-match-p "directory_files_internal (" body)) t))
  (m49-imp3--check "helper-no-policy"
                   (and (stringp body)
                        (not (string-match-p "fast_string_match\\|Fsort\\|needsep"
                                             body))
                        t)))

;; The hub rewire (brief.org section 7.3).
(m49-imp3--check "hub-calls-reader"
                 (m49-imp3--contains-p "src/dired.c"
                                       "dired_read_names_1 (directory)"))
(m49-imp3--check "hub-calls-policy"
                 (m49-imp3--contains-p
                  "src/dired.c" "scm_c_public_ref (\"emacs dired\", \"dired-listing-names\")"))
(m49-imp3--check "hub-dispatch-helper"
                 (m49-imp3--contains-p "src/dired.c"
                                       "dired_listing_names_scheme"))

(m49-imp3--check "defun-count-10"
                 (eql 10 (m49-imp3--count "src/dired.c" "^DEFUN (\"")))
(m49-imp3--check "leaf-defuns-2"
                 (eql 2 (m49-imp3--count "src/dired.c" "^DEFUN (\"--dired-")))
(m49-imp3--check "dired.c-scm-ref-2"
                 (eql 2 (m49-imp3--count "src/dired.c" "scm_c_public_ref")))
(m49-imp3--check "dired.c-lines-1346"
                 (m49-imp3--with "src/dired.c"
                   (lambda ()
                     (goto-char (point-min))
                     (let ((n 0))
                       (while (search-forward "\n" nil t) (setq n (1+ n)))
                       (eql 1346 n)))))
(m49-imp3--check "fix-marker-imp3"
                 (>= (m49-imp3--count "src/dired.c" "FIX-20261006-guilemacs") 3))

;;; --- F2. The Scheme policy (brief.org section 7.2) ------------------

(setq m49-imp3--group 'f2)

(m49-imp3--check "policy-signature"
                 (m49-imp3--contains-p
                  "mod/emacs/dired.scm"
                  "(define (dired-listing-names names directory full match nosort count)"))
(m49-imp3--check "policy-separator"
                 (m49-imp3--contains-p "mod/emacs/dired.scm" "#\\/"))
(m49-imp3--check "policy-join"
                 (m49-imp3--contains-p "mod/emacs/dired.scm" "string-append"))
;; Pin the REAL match call, not the bare token `string-match-p'.  The
;; token also occurs in the helper name and in comments, so it passes
;; even while the match data is clobbered (the D2 defect, cr.org section
;; 5.2).  The 4-argument form with INHIBIT-MODIFY = #t calls the subr
;; without changing the match data, like the old C
;; fast_string_match_internal (the D1 defect, cr.org section 5.1).
(m49-imp3--check "policy-match"
                 (m49-imp3--contains-p
                  "mod/emacs/dired.scm"
                  "((force %string-match) regexp string #nil #t)"))
(m49-imp3--check "policy-count"
                 (m49-imp3--contains-p "mod/emacs/dired.scm" "integer?"))
(m49-imp3--check "policy-sort"
                 (m49-imp3--contains-p "mod/emacs/dired.scm" "string-lessp"))
;; The 2 G2 --dired-* defelisp leaves remain after imp-4 (G3 was
;; deleted and returns A2 for G2).
(m49-imp3--check "policy-defelisp-2"
                 (eql 2 (m49-imp3--count "mod/emacs/dired.scm"
                                         "^(defelisp %--dired-")))
(m49-imp3--check "policy-no-listing-leaf"
                 (not (m49-imp3--contains-p "mod/emacs/dired.scm"
                                            "%--dired-listing-names")))
;; The public wrappers start `(define (dired-X' with a lower-case letter;
;; the private helpers start `(define (dired--'.  The `[a-z]' excludes
;; the helpers, so the count is the 4 public wrappers.
(m49-imp3--check "policy-wrappers-4"
                 (eql 4 (m49-imp3--count "mod/emacs/dired.scm"
                                         "^(define (dired-[a-z]")))
(m49-imp3--check "policy-exports-listing"
                 (m49-imp3--contains-p "mod/emacs/dired.scm"
                                       "dired-listing-names"))
(m49-imp3--check "policy-no-ffi"
                 (let ((n (m49-imp3--count-code
                           "mod/emacs/dired.scm"
                           "system foreign\\|dynamic-link\\|libc\\.so\\|system\\*\\|primitive-fork\\|posix_spawn\\|ioctl\\|dynamic-func")))
                   (and (integerp n) (eql 0 n))))
(m49-imp3--check "policy-no-scm-ref"
                 (let ((n (m49-imp3--count-code "mod/emacs/dired.scm"
                                                "scm_c_public_ref")))
                   (and (integerp n) (eql 0 n))))

;;; --- F3. The gated runtime probes (brief.org section 8) -------------

;; The (m49) group carries no `prelude' key, so tool/run-tests.scm loads
;; these files with run-tests-loadup-emacs ("../src/emacs ... -l FILE
;; --batch").  A probe calls `directory-files' DIRECTLY, in this process.
;;
;; An absent built binary is an INFO-skip.  A signalled error is a FAIL,
;; never a silent pass; the error is printed so the cause is visible.
;;
;; `directory-files' lists "." and ".." too, so the MATCH probes select a
;; deterministic subset.

(setq m49-imp3--group 'f3)

(defun m49-imp3--probe (tag thunk)
  "Register the probe TAG from the value of THUNK, which calls
`directory-files'.  A non-nil value is a PASS.  A signalled error is a
FAIL, never a silent pass; the error is printed so the cause is visible."
  (m49-imp3--check
   (format "probe/%s" tag)
   (condition-case err
       (and (funcall thunk) t)
     (error (princ (format "INFO m49/imp3/%s error=%S\n" tag err))
            nil))))

(if (not (file-exists-p (expand-file-name "src/emacs" m49-imp3--root)))
    (princ "INFO m49/imp3/runtime-probes skipped (no built src/emacs)\n")
  (m49-imp3--probe
   "match-and-sort"
   (lambda ()
     (let ((dir (file-name-as-directory (make-temp-file "m49-imp3" t))))
       (unwind-protect
           (progn
             (write-region "" nil (expand-file-name "cc" dir) nil 'silent)
             (write-region "" nil (expand-file-name "aa" dir) nil 'silent)
             (write-region "" nil (expand-file-name "bb" dir) nil 'silent)
             ;; MATCH "^[a-c]" selects aa, bb, cc (not "." or ".."),
             ;; then the sort key orders them.
             (equal '("aa" "bb" "cc") (directory-files dir nil "^[a-c]")))
         (delete-directory dir t)))))
  (m49-imp3--probe
   "match"
   (lambda ()
     (let ((dir (file-name-as-directory (make-temp-file "m49-imp3" t))))
       (unwind-protect
           (progn
             (write-region "" nil (expand-file-name "aa" dir) nil 'silent)
             (write-region "" nil (expand-file-name "ab" dir) nil 'silent)
             (write-region "" nil (expand-file-name "bb" dir) nil 'silent)
             (equal '("aa" "ab") (directory-files dir nil "a")))
         (delete-directory dir t)))))
  (m49-imp3--probe
   "match-data-preserved"
   (lambda ()
     (let ((dir (file-name-as-directory (make-temp-file "m49-imp3" t))))
       (unwind-protect
           (progn
             (write-region "" nil (expand-file-name "aa" dir) nil 'silent)
             ;; Set the match data, then call `directory-files' with a
             ;; MATCH regexp.  The policy must not clobber the match
             ;; data (the D1 defect, cr.org section 5.1).  A 2-argument
             ;; `string-match' would change it here.
             (string-match "Q" "xQy")
             (let ((before (match-data)))
               (directory-files dir nil "a")
               (equal before (match-data))))
         (delete-directory dir t)))))
  (m49-imp3--probe
   "count"
   (lambda ()
     (let ((dir (file-name-as-directory (make-temp-file "m49-imp3" t))))
       (unwind-protect
           (progn
             (write-region "" nil (expand-file-name "aa" dir) nil 'silent)
             (write-region "" nil (expand-file-name "bb" dir) nil 'silent)
             (write-region "" nil (expand-file-name "cc" dir) nil 'silent)
             ;; COUNT = 2: at most two names come back.
             (= 2 (length (directory-files dir nil "^[a-c]" nil 2))))
         (delete-directory dir t)))))
  (m49-imp3--probe
   "full"
   (lambda ()
     (let ((dir (file-name-as-directory (make-temp-file "m49-imp3" t))))
       (unwind-protect
           (progn
             (write-region "" nil (expand-file-name "aa" dir) nil 'silent)
             ;; FULL joins DIRECTORY: the name "aa" is absolute.
             (member (expand-file-name "aa" dir) (directory-files dir t)))
         (delete-directory dir t)))))
  (m49-imp3--probe
   "nosort-membership"
   (lambda ()
     (let ((dir (file-name-as-directory (make-temp-file "m49-imp3" t))))
       (unwind-protect
           (progn
             (write-region "" nil (expand-file-name "cc" dir) nil 'silent)
             (write-region "" nil (expand-file-name "aa" dir) nil 'silent)
             (let ((names (directory-files dir nil "^[a-c]" t)))
               (and (member "aa" names) (member "cc" names))))
         (delete-directory dir t))))))

;;; --- F5. The group and the guards -----------------------------------

(setq m49-imp3--group nil)

(m49-imp3--check "reg/run-tests-m49-imp3"
                 (m49-imp3--contains-p "tool/run-tests.scm"
                                       "test/m49/test-m49-imp3.el"))
;; An absent tracked file folds to the symbol `m49-imp3-absent', which is
;; distinct from t, so `m49-imp3--check' prints FAIL for it.  A
;; non-existent path stands in for an absent tracked file.
(m49-imp3--check "reg/absent-tracked-file-fails"
                 (eq 'm49-imp3-absent
                     (m49-imp3--contains-p "src/m49-imp3-no-such-file.c"
                                           "needle")))
(m49-imp3--check "reg/min-f1-checks-16"
                 (>= (m49-imp3--group-count 'f1) 16))
(m49-imp3--check "reg/min-f2-checks-12"
                 (>= (m49-imp3--group-count 'f2) 12))
(m49-imp3--check "reg/min-f3-checks-6"
                 (>= (m49-imp3--group-count 'f3) 6))

(princ (format "=== m49 imp-3 listing-policy suite done (%d tracked checks; f1 %d, f2 %d, f3 %d) ===\n"
               m49-imp3--registered
               (m49-imp3--group-count 'f1)
               (m49-imp3--group-count 'f2)
               (m49-imp3--group-count 'f3)))
