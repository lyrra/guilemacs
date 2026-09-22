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
;;; cr.org §3.1: the earlier corpus pinned #t here, a false claim.
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

;;; --- 5. Static: the module defines and exports the procedures -------
(define pio-src (slurp (repo "mod/emacs/process-io.scm")))
(check "m40/imp2/static/module-src-exists" #t (string? pio-src))
(check "m40/imp2/static/defines-string-pred" #t
       (contains? pio-src "(define (process-string-needs-encoding?"))
(check "m40/imp2/static/defines-object-pred" #t
       (contains? pio-src "(define (send-process-object-multibyte?"))
(check "m40/imp2/static/exports-string-pred" #t
       (contains? pio-src "process-string-needs-encoding?\n            send-process-object-multibyte?"))
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
