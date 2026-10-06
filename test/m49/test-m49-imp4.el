;;; test-m49-imp4.el --- M49 imp-4 corpus (the G3 attribute predicate in Scheme).
;;;
;;; M49 imp-4 moves the G3 attribute predicate of src/dired.c into
;;; (emacs dired) (brief.org section 7).  The G3 decision -- the
;;; `string-lessp' compare -- now runs in Scheme.  C keeps the mechanism
;;; and the Fcar extraction: the hub `file-attributes-lessp' reads the
;;; plain names out of the two attribute lists and calls the module.
;;;
;;; G2 (the completion policy) returns A2 (brief.org section 7.5).  The
;;; C loop decides the prefix match on encoded names with scmp, before it
;;; decodes them; Scheme holds decoded names, so a decoded match cannot
;;; replace the encoded match at an acceptable delta (brief.org section
;;; 6).  So the 2 G2 leaves and the 2 G2 hubs stay unchanged, and this
;;; corpus records that A2.
;;;
;;; This corpus reads TRACKED files only (brief.org section 8).  It pins:
;;;   F1 -- the C surface: the G3 leaf is absent; 2 --dired-* leaves
;;;         remain (both G2); the ^DEFUN count is 10; the
;;;         scm_c_public_ref count in src/dired.c is 2; the 2 G2 hubs
;;;         keep their Ffind_file_name_handler calls; the G3 dispatch
;;;         helper is static and holds no decision.
;;;   F2 -- the Scheme policy: the module computes the compare with
;;;         `string-lessp' and returns #t / #nil; the defelisp %--dired-
;;;         count is 2; the module holds no FFI and no scm_c_public_ref.
;;;   F3 -- the G3 slot: `file-attributes-lessp' keeps the Fcar
;;;         extraction and calls the Scheme predicate.
;;;   F4 -- the runtime probes: run the built src/emacs.  Probe
;;;         `file-name-completion', `file-name-all-completions', and
;;;         `file-attributes-lessp' over temp directories.  Pin the sole
;;;         exact match returns t, the longest common prefix, the sort
;;;         key, and the directory "/" suffix.
;;;   F5 -- the group and the guards: the (m49) group carries this
;;;         corpus, and a per-group min-count guard fails when the corpus
;;;         is truncated.
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real error.  This corpus reads no docs/ needle
;;; (docs/kb.org test-must-not-read-docs).  The probe error is a FAIL,
;;; never a silent pass (docs/kb.org
;;; m4x-probe-failure-must-not-read-as-a-skip).

(princ "=== m49 imp-4 attribute-predicate suite ===\n")

(require 'imp-ert-report)

(defvar m49-imp4--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m49-imp4--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m49-imp4--group nil
  "The group that `m49-imp4--check' counts into: `f1' ... `f4', or nil.")

(defvar m49-imp4--counts nil
  "Alist of (GROUP . COUNT) for the registered tracked-file checks.")

(defun m49-imp4--group-count (group)
  "Number of tracked-file checks registered so far in GROUP."
  (or (cdr (assq group m49-imp4--counts)) 0))

(defun m49-imp4--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m49-imp4-absent' when REL does not exist."
  (let ((path (expand-file-name rel m49-imp4--root)))
    (if (not (file-exists-p path))
        'm49-imp4-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m49-imp4--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m49-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m49-imp4--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m49-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m49-imp4--count-code (rel regexp)
  "Count the matches of REGEXP in REL, skipping full comment lines.
A module comment may name a forbidden token while explaining the
contract; only the code must be free of the token.  Scheme line comments
start with `;'."
  (m49-imp4--with rel
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

(defun m49-imp4--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
An absent src/ file makes the reader return the symbol
`m49-imp4-absent', so the check prints FAIL -- an absent src/ file is a
real error, not a pass."
  (if (eq ok 'm49-imp4-absent)
      (princ (format "INFO m49/imp4/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m49/imp4/%s\n" (if ok "PASS" "FAIL") name))
      (setq m49-imp4--registered (1+ m49-imp4--registered))
      (when m49-imp4--group
        (let ((cell (assq m49-imp4--group m49-imp4--counts)))
          (if cell
              (setcdr cell (1+ (cdr cell)))
            (push (cons m49-imp4--group 1) m49-imp4--counts))))
      (imp-register-bool-as-ert-test (format "m49-imp4/%s" name) (and ok t)))))

(defun m49-imp4--fn-body (name)
  "Return the C source of the function NAME in src/dired.c, from the
line before its name (the return-type line, so `static' is included) to
the closing `\\n}' at column 0, or nil."
  (m49-imp4--with "src/dired.c"
    (lambda ()
      (goto-char (point-min))
      (when (search-forward (concat "\n" name " (") nil t)
        (let ((start (save-excursion (forward-line -1) (line-beginning-position))))
          (if (search-forward "\n}" nil t)
              (buffer-substring-no-properties start (match-end 0))
            (buffer-substring-no-properties start (point-max))))))))

(defun m49-imp4--defun-body (name)
  "Return the source of DEFUN (\"NAME\"...) up to its closing \"\\n}\"."
  (m49-imp4--with "src/dired.c"
    (lambda ()
      (goto-char (point-min))
      (when (re-search-forward (format "DEFUN (\"%s\"" (regexp-quote name)) nil t)
        (let ((start (line-beginning-position)))
          (if (search-forward "\n}" nil t)
              (buffer-substring-no-properties start (match-end 0))
            (buffer-substring-no-properties start (point-max))))))))

;;; --- F1. The C surface (brief.org section 7.1 and section 7.3) ------

(setq m49-imp4--group 'f1)

;; The deleted G3 leaf: no token of it may remain (brief.org section 7.3).
(m49-imp4--check "g3-leaf-token-absent"
                 (not (m49-imp4--contains-p "src/dired.c"
                                            "--dired-file-attributes-lessp")))
(m49-imp4--check "g3-leaf-fname-token-absent"
                 (not (m49-imp4--contains-p "src/dired.c"
                                            "Fdired_file_attributes_lessp")))

;; The 2 G2 leaves stay (G2 returns A2).
(m49-imp4--check "g2-leaf-completion-present"
                 (m49-imp4--contains-p "src/dired.c"
                                       "DEFUN (\"--dired-file-name-completion\""))
(m49-imp4--check "g2-leaf-all-completions-present"
                 (m49-imp4--contains-p
                  "src/dired.c" "DEFUN (\"--dired-file-name-all-completions\""))

(m49-imp4--check "defun-count-10"
                 (eql 10 (m49-imp4--count "src/dired.c" "^DEFUN (\"")))
(m49-imp4--check "leaf-defuns-2"
                 (eql 2 (m49-imp4--count "src/dired.c" "^DEFUN (\"--dired-")))
(m49-imp4--check "dired.c-scm-ref-2"
                 (eql 2 (m49-imp4--count "src/dired.c" "scm_c_public_ref")))

;; The 2 G2 hubs keep their own handler dispatch (brief.org section 4:
;; handler-call-is-not-a-leaf).
(let ((body (m49-imp4--defun-body "file-name-completion")))
  (m49-imp4--check "g2-hub-completion-keeps-handler"
                   (and (stringp body)
                        (string-match-p "Ffind_file_name_handler" body) t)))
(let ((body (m49-imp4--defun-body "file-name-all-completions")))
  (m49-imp4--check "g2-hub-all-keeps-handler"
                   (and (stringp body)
                        (string-match-p "Ffind_file_name_handler" body) t)))

;; The G3 dispatch helper is static and holds no decision.
(let ((body (m49-imp4--fn-body "dired_file_attributes_lessp_scheme")))
  (m49-imp4--check "g3-helper-static"
                   (and (stringp body)
                        (string-match-p "static Lisp_Object" body) t))
  (m49-imp4--check "g3-helper-calls-module"
                   (and (stringp body)
                        (string-match-p "dired-file-attributes-lessp" body) t))
  (m49-imp4--check "g3-helper-no-decision"
                   (and (stringp body)
                        (not (string-match-p "Fstring_lessp" body)) t))
  ;; The helper calls the module, not its own hub (leaf-must-call-the-
  ;; mechanism).
  (m49-imp4--check "g3-helper-no-hub"
                   (and (stringp body)
                        (not (string-match-p "Ffile_attributes_lessp (" body))
                        t)))

(m49-imp4--check "fix-marker-imp4"
                 (>= (m49-imp4--count "src/dired.c" "FIX-20261006-guilemacs") 1))

;;; --- F2. The Scheme policy (brief.org section 7.4) ------------------

(setq m49-imp4--group 'f2)

(m49-imp4--check "policy-signature"
                 (m49-imp4--contains-p
                  "mod/emacs/dired.scm"
                  "(define (dired-file-attributes-lessp name1 name2)"))
;; The decision runs in Scheme: the compare is `string-lessp', reached by
;; the module helper, and the result crosses back as elisp t / nil.
(m49-imp4--check "policy-string-lessp"
                 (m49-imp4--contains-p "mod/emacs/dired.scm"
                                       "(dired--string-lessp name1 name2)"))
(m49-imp4--check "policy-plain-bool"
                 (m49-imp4--contains-p
                  "mod/emacs/dired.scm"
                  "(if (dired--string-lessp name1 name2) #t #nil)"))
(m49-imp4--check "policy-no-g3-leaf"
                 (not (m49-imp4--contains-p "mod/emacs/dired.scm"
                                            "%--dired-file-attributes-lessp")))
(m49-imp4--check "policy-defelisp-2"
                 (eql 2 (m49-imp4--count "mod/emacs/dired.scm"
                                         "^(defelisp %--dired-")))
(m49-imp4--check "policy-exports"
                 (m49-imp4--contains-p "mod/emacs/dired.scm"
                                       "dired-file-attributes-lessp"))
(m49-imp4--check "policy-no-ffi"
                 (let ((n (m49-imp4--count-code
                           "mod/emacs/dired.scm"
                           "system foreign\\|dynamic-link\\|libc\\.so\\|system\\*\\|primitive-fork\\|posix_spawn\\|ioctl\\|dynamic-func")))
                   (and (integerp n) (eql 0 n))))
(m49-imp4--check "policy-no-scm-ref"
                 (let ((n (m49-imp4--count-code "mod/emacs/dired.scm"
                                                "scm_c_public_ref")))
                   (and (integerp n) (eql 0 n))))

;;; --- F3. The G3 slot (brief.org section 7.3) ------------------------

(setq m49-imp4--group 'f3)

;; The hub keeps the Fcar extraction (the attribute list must not cross
;; the layer) and calls the Scheme predicate.
(m49-imp4--check "hub-keeps-fcar"
                 (m49-imp4--contains-p "src/dired.c" "Fcar (f1), Fcar (f2)"))
(m49-imp4--check "hub-calls-dispatch-helper"
                 (m49-imp4--contains-p "src/dired.c"
                                       "dired_file_attributes_lessp_scheme (Fcar"))
(m49-imp4--check "hub-policy-ref"
                 (m49-imp4--contains-p
                  "src/dired.c"
                  "scm_c_public_ref (\"emacs dired\", \"dired-file-attributes-lessp\")"))
;; The hub takes two attribute lists, not two names.
(m49-imp4--check "hub-signature-f1-f2"
                 (m49-imp4--contains-p
                  "src/dired.c" "(Lisp_Object f1, Lisp_Object f2)"))

;;; --- F4. The gated runtime probes (brief.org section 8) -------------

;; The (m49) group carries no `prelude' key, so tool/run-tests.scm loads
;; these files with run-tests-loadup-emacs ("../src/emacs ... -l FILE
;; --batch").  A probe calls the hub DIRECTLY, in this process.
;;
;; An absent built binary is an INFO-skip.  A signalled error is a FAIL,
;; never a silent pass; the error is printed so the cause is visible.

(setq m49-imp4--group 'f4)

(defun m49-imp4--probe (tag thunk)
  "Register the probe TAG from the value of THUNK, which calls a hub.
A non-nil value is a PASS.  A signalled error is a FAIL, never a silent
pass; the error is printed so the cause is visible."
  (m49-imp4--check
   (format "probe/%s" tag)
   (condition-case err
       (and (funcall thunk) t)
     (error (princ (format "INFO m49/imp4/%s error=%S\n" tag err))
            nil))))

(defun m49-imp4--with-tmpdir (tag body)
  "Call BODY with a fresh temp directory, then delete it.  BODY calls
`file-name-completion' / `file-name-all-completions' directly."
  (let ((dir (file-name-as-directory (make-temp-file "m49-imp4" t))))
    (unwind-protect (funcall body dir) (delete-directory dir t))))

(if (not (file-exists-p (expand-file-name "src/emacs" m49-imp4--root)))
    (princ "INFO m49/imp4/runtime-probes skipped (no built src/emacs)\n")
  (m49-imp4--probe
   "completion-sole-exact-match-t"
   (lambda ()
     (m49-imp4--with-tmpdir "exact"
       (lambda (dir)
         (write-region "" nil (expand-file-name "only.txt" dir) nil 'silent)
         ;; The sole exact match returns t.
         (eq t (file-name-completion "only.txt" dir))))))
  (m49-imp4--probe
   "completion-longest-common-prefix"
   (lambda ()
     (m49-imp4--with-tmpdir "prefix"
       (lambda (dir)
         (write-region "" nil (expand-file-name "abcd" dir) nil 'silent)
         (write-region "" nil (expand-file-name "abce" dir) nil 'silent)
         ;; The longest common prefix of "abcd" and "abce" is "abc".
         (equal "abc" (file-name-completion "ab" dir))))))
  (m49-imp4--probe
   "completion-directory-slash"
   (lambda ()
     (m49-imp4--with-tmpdir "slash"
       (lambda (dir)
         (make-directory (expand-file-name "onlydir" dir))
         ;; A partial that matches only a directory completes to
         ;; "onlydir/" (the directory "/" suffix).
         (equal "onlydir/" (file-name-completion "onl" dir))))))
  (m49-imp4--probe
   "all-completions-sort-key"
   (lambda ()
     (m49-imp4--with-tmpdir "sort"
       (lambda (dir)
         (write-region "" nil (expand-file-name "aa" dir) nil 'silent)
         (write-region "" nil (expand-file-name "ab" dir) nil 'silent)
         (write-region "" nil (expand-file-name "bb" dir) nil 'silent)
         ;; The all-completions list holds the matches, sorted by
         ;; `string-lessp'.
         (equal '("aa" "ab") (file-name-all-completions "a" dir))))))
  (m49-imp4--probe
   "attributes-lessp-true"
   (lambda ()
     ;; The hub takes two attribute lists, extracts Fcar, and the Scheme
     ;; predicate decides the compare.
     (eq t (file-attributes-lessp '("a") '("b")))))
  (m49-imp4--probe
   "attributes-lessp-false"
   (lambda ()
     (eq nil (file-attributes-lessp '("b") '("a"))))))

;;; --- F5. The group and the guards -----------------------------------

(setq m49-imp4--group nil)

(m49-imp4--check "reg/run-tests-m49-imp4"
                 (m49-imp4--contains-p "tool/run-tests.scm"
                                       "test/m49/test-m49-imp4.el"))
;; An absent tracked file folds to the symbol `m49-imp4-absent', which is
;; distinct from t, so `m49-imp4--check' prints FAIL for it.
(m49-imp4--check "reg/absent-tracked-file-fails"
                 (eq 'm49-imp4-absent
                     (m49-imp4--contains-p "src/m49-imp4-no-such-file.c"
                                           "needle")))
(m49-imp4--check "reg/min-f1-checks-12"
                 (>= (m49-imp4--group-count 'f1) 12))
(m49-imp4--check "reg/min-f2-checks-7"
                 (>= (m49-imp4--group-count 'f2) 7))
(m49-imp4--check "reg/min-f3-checks-4"
                 (>= (m49-imp4--group-count 'f3) 4))
(m49-imp4--check "reg/min-f4-checks-6"
                 (>= (m49-imp4--group-count 'f4) 6))

(princ (format "=== m49 imp-4 attribute-predicate suite done (%d tracked checks; f1 %d, f2 %d, f3 %d, f4 %d) ===\n"
               m49-imp4--registered
               (m49-imp4--group-count 'f1)
               (m49-imp4--group-count 'f2)
               (m49-imp4--group-count 'f3)
               (m49-imp4--group-count 'f4)))
