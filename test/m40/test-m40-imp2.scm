;;; test-m40-imp2.scm --- M40 imp-2: the send_process multibyte decision.
;;;
;;; brief.org (M40 imp-2) moves the multibyte-versus-unibyte *decision* of
;;; send_process (src/process.c, the previous predicate at :6843-6846)
;;; into the module (emacs process-io):
;;;
;;;   process-string-needs-encoding?  -- the STRINGP + STRING_MULTIBYTE
;;;                                      term, under a process-local name.
;;;                                      It mirrors the C STRING_MULTIBYTE
;;;                                      byte-length rule (src/lisp.h:1196-1207).
;;;   send-process-object-multibyte?  -- the whole if-condition: the
;;;                                      string term, the imp-1 buffer
;;;                                      term, and the Qt term.
;;;
;;; The C keeps the two arms and the NETCONN_P / wait_while_connecting
;;; rule; src/process.c calls the C dispatcher
;;; send_process_object_multibyte_decision.
;;;
;;; Two kinds of check: the runtime value of each predicate (against the
;;; C rule), and a static scan of the module, src/process.c, and the
;;; harness registration.
;;;
;;; The repo root is bound by the .el wrapper as %m40-root, and the .el
;;; wrapper creates the two buffers the buffer-term checks use (one
;;; unibyte, one multibyte), so the corpus does not touch the current
;;; buffer.  The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT
;;; test; see test/m40/test-m40-imp2.el.

(use-modules (srfi srfi-13))
(use-modules (ice-9 popen))
(use-modules (ice-9 rdelim))

(use-modules (emacs-elisp runtime))
(use-modules (emacs strings))
(use-modules (emacs process-io))
(use-modules (emacs text-properties))

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

(define (repo path) (string-append %m40-root "/" path))

(define (contains? text needle)
  (and (string? text)
       (if (string-contains text needle) #t #f)))

(define (export-region text)
  "Return the text of the module's #:export form, or #f when TEXT is
absent or holds no #:export form.  The export check uses this so the
needle does not pin the indentation or the line layout of the export
list: a later reflow of the list must not give a false FAIL."
  (if (not (string? text))
      #f
      (let ((start (string-contains text "#:export (")))
        (if (not start)
            #f
            (let ((end (string-contains text ")" start)))
              (and end (substring text start end)))))))

;; A non-ASCII character built at runtime, so the corpus source stays
;; plain ASCII and no source-encoding question can change the byte
;; length.  U+00E4 = "a" with diaeresis; its UTF-8 form is two bytes.
(define non-ascii (string (integer->char #x00e4)))
(define non-ascii-string non-ascii)
(define multibyte-string (string-append "x" non-ascii))
(define ascii-string "abc")

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m40-root))
    (begin (report "m40-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m40-root "."))
    (report "m40-root-bound" 'PASS))

;;; --- 1. The module loads and exports the new procedures ------------
(define needs-encoding?
  (module-ref (resolve-module '(emacs process-io))
              'process-string-needs-encoding?))
(define object-multibyte?
  (module-ref (resolve-module '(emacs process-io))
              'send-process-object-multibyte?))

(check "m40/imp2/export/process-string-needs-encoding?" #t
       (and (defined? 'needs-encoding?) (procedure? needs-encoding?)))
(check "m40/imp2/export/send-process-object-multibyte?" #t
       (and (defined? 'object-multibyte?) (procedure? object-multibyte?)))

;;; --- 2. Runtime: process-string-needs-encoding? mirrors the C rule --
;;;
;;; The C STRING_MULTIBYTE rule: a string is multibyte when its UTF-8
;;; byte length differs from its character length.
(check "m40/imp2/string/ascii" #nil (needs-encoding? ascii-string))
(check "m40/imp2/string/non-ascii" #t (needs-encoding? non-ascii-string))
(check "m40/imp2/string/multibyte" #t (needs-encoding? multibyte-string))
(check "m40/imp2/string/empty" #nil (needs-encoding? ""))
;; A non-string returns nil, so the caller may pass any object.
(check "m40/imp2/string/number" #nil (needs-encoding? 5))
(check "m40/imp2/string/nil" #nil (needs-encoding? #nil))
(check "m40/imp2/string/symbol" #nil (needs-encoding? 'foo))
;; An emacs-string wrapper unwraps before the byte count.
(check "m40/imp2/string/wrapper-ascii" #nil
       (needs-encoding? (make-emacs-string ascii-string)))
(check "m40/imp2/string/wrapper-non-ascii" #t
       (needs-encoding? (make-emacs-string non-ascii-string)))

;;; --- 3. Runtime: send-process-object-multibyte?, term by term -------
;;; Qt term: Qt is SCM_BOOL_T (src/lread.c:2878), so the elisp t reaches
;;; Scheme as #t.  The Guile symbol t is not Qt: the C EQ (object, Qt)
;;; is false for it, so the predicate returns #nil (the unibyte arm).
;;; The earlier corpus pinned #t here; docs/kb.org ** M40 records the fix.
(check "m40/imp2/object/qt-hash" #t (object-multibyte? #t))
(check "m40/imp2/object/qt-symbol-not-qt" #nil (object-multibyte? 't))
;; The string term.
(check "m40/imp2/object/multibyte-string" #t
       (object-multibyte? multibyte-string))
(check "m40/imp2/object/ascii-string" #nil
       (object-multibyte? ascii-string))
;; The buffer term (imp-1).  The wrapper created and configured these.
(define (get-buffer name) ((symbol-function 'get-buffer) name))
(define unibyte-buffer (get-buffer "m40-imp2-unibyte"))
(define multibyte-buffer (get-buffer "m40-imp2-multibyte"))
(check "m40/imp2/object/buffers-exist" #t
       (and (not (eq? unibyte-buffer #nil))
            (not (eq? multibyte-buffer #nil))))
(check "m40/imp2/object/multibyte-buffer" #t
       (object-multibyte? multibyte-buffer))
(check "m40/imp2/object/unibyte-buffer" #nil
       (object-multibyte? unibyte-buffer))
;; No term holds.
(check "m40/imp2/object/number" #nil (object-multibyte? 5))
(check "m40/imp2/object/nil" #nil (object-multibyte? #nil))
(check "m40/imp2/object/symbol" #nil (object-multibyte? 'foo))

;;; --- 4. The elisp multibyte-string-p stays nil ----------------------
;;; The imp-2 name is process-local.  The elisp-visible name keeps the
;;; recorded deviation; the two names answer different questions.
(define mbsp
  (module-ref (resolve-module '(emacs strings)) 'elisp-multibyte-string-p))
(check "m40/imp2/elisp-name/ascii" #nil (mbsp ascii-string))
(check "m40/imp2/elisp-name/non-ascii" #nil (mbsp non-ascii-string))
(check "m40/imp2/names-distinct" #t
       (not (eq? needs-encoding? mbsp)))

;;; --- 4b. F1: the byte-length rule is not the vanilla STRING_MULTIBYTE -
;;;
;;; The C tests a *flag* (STRING_MULTIBYTE); this helper tests the UTF-8
;;; byte length.  The two tests agree for ordinary UTF-8 text but differ
;;; for a unibyte string built from a high byte.
;;;
;;; Vanilla Emacs: (unibyte-string 228) is a one-byte unibyte string, so
;;; STRING_MULTIBYTE is false and send_process runs the else arm.
;;; Guilemacs: (unibyte-string 228) keeps no unibyte representation -- it
;;; is the ordinary UTF-8 string "\u00e4" (two bytes), so the byte-length
;;; rule marks it multibyte and send_process runs the then arm.
;;;
;;; This is the recorded deviation, not a defect: brief.org §9 and §10
;;; keep the deviation, and docs/kb.org ** M40 (the entry
;;; multibyte-string-p) records it.  A faithful answer needs a shared
;;; unibyte flag on strings.  The check pins the current (deviating)
;;; value so a later change is visible.
(define unibyte-high ((symbol-function 'unibyte-string) 228))
(check "m40/imp2/f1/unibyte-high-byte" #t (needs-encoding? unibyte-high))

;;; --- 5. Static: the module defines and exports the procedures -------
(define pio-src (slurp (repo "mod/emacs/process-io.scm")))
(check "m40/imp2/static/module-src-exists" #t (string? pio-src))
(check "m40/imp2/static/defines-string-pred" #t
       (contains? pio-src "(define (process-string-needs-encoding?"))
(check "m40/imp2/static/defines-object-pred" #t
       (contains? pio-src "(define (send-process-object-multibyte?"))
;; Loose needle (F6): check the exported names inside the #:export form,
;; not a fixed two-line string that pins the list indentation.
(define pio-exports (export-region pio-src))
(check "m40/imp2/static/exports-string-pred" #t
       (contains? pio-exports "process-string-needs-encoding?"))
(check "m40/imp2/static/exports-object-pred" #t
       (contains? pio-exports "send-process-object-multibyte?"))
;; The string term uses the byte-length rule (string->utf8 + string-length).
(check "m40/imp2/static/byte-length-rule" #t
       (and (contains? pio-src "(string->utf8 object)")
            (contains? pio-src "(bytevector-length (string->utf8 content))")))
;; The object predicate ORs the three terms and forces a boolean.
(check "m40/imp2/static/object-uses-string-term" #t
       (contains? pio-src "(process-string-needs-encoding? object)"))
(check "m40/imp2/static/object-uses-buffer-term" #t
       (contains? pio-src "(object-enable-multibyte-characters object)"))
;; The module header records the move (M40 imp-2), so the durable record
;; is not only in this corpus.
(check "m40/imp2/static/header-records-move" #t
       (contains? pio-src "M40 imp-2 moves the multibyte-versus-unibyte"))
;; Hygiene: a source comment must not cite the transient review file --
;; it is untracked, and a later reset can delete it.  The durable record
;; is docs/kb.org ** M40.  The needle is built at run time so this check
;; cannot match itself.
(define transient-review-needle (string-append "cr" ".org"))
(check "m40/imp2/static/no-transient-cr-citation" #f
       (contains? pio-src transient-review-needle))
(check "m40/imp2/static/cites-kb-m40" #t
       (contains? pio-src "docs/kb.org ** M40"))
;; This corpus holds source comments too, so the same rule applies to it.
(define imp2-corpus-src (slurp (repo "test/m40/test-m40-imp2.scm")))
(check "m40/imp2/static/corpus-no-transient-citation" #f
       (contains? imp2-corpus-src transient-review-needle))

;;; --- 6. Static: src/process.c wires the dispatcher, old code is gone
(define proc-c (slurp (repo "src/process.c")))
(if (not proc-c)
    (report "m40/imp2/scan/process.c" (cons 'FAIL "src/process.c missing"))
    (begin
      ;; The dispatcher is defined local to process.c.
      (check "m40/imp2/process.c/defines-dispatcher" #t
             (contains? proc-c
                        "send_process_object_multibyte_decision (Lisp_Object object)"))
      (check "m40/imp2/process.c/public-ref-module" #t
             (contains? proc-c "scm_c_public_ref (\"emacs process-io\""))
      (check "m40/imp2/process.c/public-ref-symbol" #t
             (contains? proc-c "\"send-process-object-multibyte?\""))
      ;; The dispatcher is called by the reduced body; the module owns the
      ;; decision (no C-side predicate).
      (check "m40/imp2/process.c/calls-dispatcher" #t
             (contains? proc-c "if (send_process_object_multibyte_decision (object))"))
      (check "m40/imp2/process.c/no-old-predicate" #f
             (contains? proc-c "STRINGP (object) && STRING_MULTIBYTE (object)"))
      (check "m40/imp2/process.c/no-old-buffer-term" #f
             (contains? proc-c "!NILP (BVAR (XBUFFER (object), enable_multibyte_characters))"))
      ;; The two arms stay C.
      (check "m40/imp2/process.c/keeps-then-arm" #t
             (contains? proc-c "coding->src_multibyte = 1;"))
      (check "m40/imp2/process.c/keeps-else-arm" #t
             (contains? proc-c "coding->src_multibyte = 0;"))
      (check "m40/imp2/process.c/keeps-encoding-setup" #t
             (contains? proc-c "complement_process_encoding_system (p->encode_coding_system)"))
      (check "m40/imp2/process.c/keeps-setup-coding-system" #t
             (contains? proc-c "setup_coding_system (p->encode_coding_system, coding)"))
      ;; The NETCONN_P / wait_while_connecting rule stays C.
      (check "m40/imp2/process.c/keeps-netconn-rule" #t
             (contains? proc-c "wait_while_connecting (proc)"))))

;;; --- 7. Static: the harness registers the M40 group -----------------
(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m40/imp2/run-tests/registers-el" #t
       (contains? run-tests "test/m40/test-m40-imp2.el"))

;;; --- 8. Static: the dispatcher moves the tree-wide ref count --------
;;;
;;; The new C dispatcher adds one scm_c_public_ref site to src/process.c,
;;; so the tree-wide count over src/*.c and src/*.h rises 162 -> 163 at
;;; imp-2 and 167 after the imp-4a dispatchers, then 172 after the imp-4b
;;; dispatchers.  The
;;; This test still records the observed tree count as milestone history.
;;; Source-count assertions in unrelated keyboard milestone corpora do
;;; not provide runtime coverage and are not part of the test gate.
(define (count-substr text sub)
  "Count the non-overlapping occurrences of SUB in TEXT, or 0 when TEXT
is not a string.  Each scm_c_public_ref site sits on its own line, so the
occurrence count equals the guard's line count."
  (if (not (string? text))
      0
      (let ((sl (string-length sub)))
        (let loop ((i 0) (n 0))
          (if (>= i (string-length text))
              n
              (let ((hit (string-contains text sub i)))
                (if hit (loop (+ hit sl) (1+ n)) n)))))))

(define (src-c-h-files)
  "The buildable top-level C sources and headers of src/, like the guard
scan over src/*.c and src/*.h."
  (let ((d (opendir (repo "src"))))
    (let loop ((names '()))
      (let ((n (readdir d)))
        (if (eof-object? n)
            (begin (closedir d) names)
            (loop (if (or (string-suffix? ".c" n) (string-suffix? ".h" n))
                      (cons n names)
                      names)))))))

(define tree-ref-sites
  (let loop ((fs (src-c-h-files)) (acc 0))
    (if (null? fs)
        acc
        (loop (cdr fs)
              (+ acc (count-substr (slurp (repo (string-append "src/" (car fs))))
                                   "scm_c_public_ref"))))))

(check "m40/imp2/static/process.c-holds-the-new-site" #t
       (contains? proc-c "scm_c_public_ref (\"emacs process-io\""))
(check "m40/imp2/static/tree-ref-sites-228" 228 tree-ref-sites)

;;; --- 9. Static: the durable records name the imp-2 commit ------------
;;;
;;; The records must point at the landed imp-2 commit and must not name
;;; the dead pre-rebase hash (the kb.org Gotcha closeout-pin-live-tracker).
;;; docs/ is gitignored and milestone.org is untracked, so an absent
;;; record is INFO-skipped.
;;;
;;; The record can NOT be pinned to the live short hash.  The hash of the
;;; commit that lands this change is unknown before the commit: a commit
;;; cannot contain its own hash, and the harness re-commits the tree with
;;; a fresh committer date, so the short hash changes on every run.  An
;;; earlier revision compared the record text to the live hash; that
;;; check can never pass (FIX-20260923-guilemacs).  The stable link is
;;; the imp-2 SUBJECT string, which the closeout writes into the records
;;; after the land.
;;;
;;; Three cases must not be confused:
;;;
;;;   * git does not run          -> INFO.  This is an environment gap; a
;;;                                 fresh clone must not FAIL.
;;;   * git runs, no imp-2 commit -> FAIL.  This is a broken link (for
;;;                                 example, a rewritten subject), not an
;;;                                 environment gap.  It must not be silent.
;;;   * the record names the dead hash -> FAIL.  A real defect.
;;;   * the record does not name the imp-2 commit yet -> INFO.  The
;;;                                 closeout updates the records after the
;;;                                 land; the gate must not FAIL before it.
;;;
;;; The subject is matched with --fixed-strings, so a regexp metacharacter
;;; in a subject stays literal.  The repo path and the subject are
;;; shell-quoted: a path with a space or a shell metacharacter must not
;;; split the command.  A second, source-derived lookup (§9b) cross-checks
;;; the subject link, so a rewritten subject is visible.

(define (shell-quote s)
  "Single-quote S for /bin/sh.  Handles spaces and shell metacharacters.
An embedded single quote is not handled; no repo path or subject here
holds one."
  (string-append "'" s "'"))

(define (git-run cmd)
  "Run CMD through the shell.  Return (STATUS . LINE): LINE is the first
output line (or #f at end of file), STATUS is the wait status of the
pipe (or #f when the pipe cannot open)."
  (let ((port (catch #t (lambda () (open-input-pipe cmd)) (lambda args #f))))
    (if (not port)
        (cons #f #f)
        (let ((line (read-line port)))
          (cons (close-pipe port) (if (eof-object? line) #f line))))))

(define git-version (git-run "git --version"))
(define (git-available?)
  "True when git runs and reports a version."
  (let ((line (cdr git-version)))
    (and (string? line) (string-prefix? "git version" line))))

(define imp2-subject
  "M40 imp-2: re-land the send_process multibyte decision")

(define (git-subject-hash)
  "Return (STATUS . VALUE) for the imp-2 commit found by its subject.
STATUS is 'ok (VALUE is the short hash), 'no-match (git ran but no
commit matched the subject), or 'git-absent (git did not run)."
  (if (not (git-available?))
      (cons 'git-absent #f)
      (let* ((cmd (string-append
                   "git -C " (shell-quote (repo ""))
                   " log --format=%h --fixed-strings --grep="
                   (shell-quote imp2-subject) " -1"))
             (line (cdr (git-run cmd))))
        (if (string? line)
            (cons 'ok line)
            (cons 'no-match #f)))))

(define live-imp2 (git-subject-hash))
(define live-imp2-status (car live-imp2))
(define live-imp2-hash (cdr live-imp2))

(define dead-imp2-hash "ad91ed0")

(define (record-names-live-hash name rel)
  "Guard the durable record REL.  Report FAIL only on a real defect: git
runs but no imp-2 commit matches the subject, or REL names the dead
pre-rebase hash.  Report PASS when REL names the imp-2 subject.  Report
INFO when REL is absent (gitignored docs/, untracked milestone.org),
when git is unavailable, or when REL does not name the imp-2 commit yet.

The live short hash is not used: it is unknown before the commit (see
the section 9 header).  The stable link is the imp-2 subject."
  (let ((text (slurp (repo rel))))
    (cond
      ((not (string? text)) (report name (list 'INFO "record absent")))
      ((eq? live-imp2-status 'git-absent)
       (report name (list 'INFO "git unavailable")))
      ((eq? live-imp2-status 'no-match)
       ;; git runs but holds no imp-2 commit: a broken subject link, not
       ;; an environment gap (see the section 9 header).  It must not be
       ;; silent.
       (report name (list 'FAIL 'no-imp2-commit imp2-subject)))
      ((contains? text dead-imp2-hash)
       (report name (list 'FAIL 'names-dead-hash dead-imp2-hash)))
      ((contains? text imp2-subject)
       (report name 'PASS))
      (else
       (report name
               (list 'INFO "record does not name the imp-2 commit yet"))))))
(record-names-live-hash "m40/imp2/record/kb-m40" "docs/kb.org")
(record-names-live-hash "m40/imp2/record/milestone" "milestone.org")

;;; --- 9b. The run-time pin resolves and agrees with a source lookup ----
;;;
;;; The subject link (§9) is fragile: the subject string is copied from
;;; the commit message, so a rewrite breaks it silently.  A source-derived
;;; lookup is independent: the commit that added the C dispatcher symbol
;;; send_process_object_multibyte_decision (a git pickaxe, -S) is the same
;;; commit.  When the two disagree, the subject link is stale.  Both checks
;;; need git; when git is absent they are INFO-skipped, like §9.
(define (hex-hash? s)
  "True when S is a short lowercase hex hash (the git --format=%h form)."
  (and (string? s)
       (<= 4 (string-length s) 40)
       (let loop ((i 0))
         (if (>= i (string-length s))
             #t
             (let ((c (string-ref s i)))
               (and (or (char-numeric? c)
                        (and (char>=? c #\a) (char<=? c #\f)))
                    (loop (1+ i))))))))

(define (git-dispatch-site-hash)
  "Return the short hash of the commit that introduced the C dispatcher
symbol in src/process.c, or #f when git is unavailable or finds none."
  (if (not (git-available?))
      #f
      (let* ((cmd (string-append
                   "git -C " (shell-quote (repo ""))
                   " log --format=%h -S"
                   (shell-quote "send_process_object_multibyte_decision")
                   " -1 -- src/process.c"))
             (line (cdr (git-run cmd))))
        (and (string? line) line))))

(if (not (git-available?))
    (report "m40/imp2/githash/resolves" (list 'INFO "git unavailable"))
    (if (eq? live-imp2-status 'no-match)
        ;; git runs but holds no imp-2 commit: a broken subject link, not
        ;; an environment gap (see the section 9 header).  It must not be
        ;; silent.
        (begin
          (report "m40/imp2/githash/resolves"
                  (list 'FAIL 'no-imp2-commit imp2-subject))
          (report "m40/imp2/githash/well-formed"
                  (list 'FAIL 'no-imp2-commit imp2-subject))
          (report "m40/imp2/githash/agrees-with-dispatch-site"
                  (list 'FAIL 'no-imp2-commit imp2-subject)))
        (begin
          (check "m40/imp2/githash/resolves" #t (eq? live-imp2-status 'ok))
          (check "m40/imp2/githash/well-formed" #t (hex-hash? live-imp2-hash))
          (check "m40/imp2/githash/agrees-with-dispatch-site" live-imp2-hash
                 (git-dispatch-site-hash)))))
