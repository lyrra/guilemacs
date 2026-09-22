;;; test-m40-imp1.scm --- M40 imp-1: faithful multibyte predicates.
;;;
;;; brief.org (M40 imp-1) names two predicates for M40 imp-2, and adds
;;; no C:
;;;
;;;   - multibyte-string-p (mod/emacs/strings.scm,
;;;     elisp-multibyte-string-p).  Guilemacs keeps no unibyte string
;;;     representation, so the predicate returns nil for every object.
;;;     That is a recorded deviation, FIX-20260921-guilemacs.  Section 1
;;;     pins it and records why a byte-length rule is wrong;
;;;   - a buffer read of enable-multibyte-characters
;;;     (mod/emacs/process-io.scm, object-enable-multibyte-characters):
;;;     it takes a buffer argument, because the send_process predicate
;;;     reads XBUFFER (object), not the current buffer.
;;;
;;; Two kinds of check: the runtime value of each predicate, and a
;;; static scan of the two modules and the harness registration.
;;;
;;; The repo root is bound by the .el wrapper as %m40-root, and the .el
;;; wrapper creates the two buffers the buffer-read checks use (one
;;; unibyte, one multibyte), so the corpus does not touch the current
;;; buffer.  The .el wrapper turns each (NAME PASS|FAIL) pair into an
;;; ERT test; see test/m40/test-m40-imp1.el.

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

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m40-root))
    (begin (report "m40-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m40-root "."))
    (report "m40-root-bound" 'PASS))

;;; --- 1. multibyte-string-p records a deviation ---------------------
;;;
;;; The first draft of this imp asserted a "faithful" rule: a string is
;;; multibyte when its UTF-8 byte length differs from its character
;;; length.  That rule is not faithful, and it broke
;;; test/lisp/emacs-lisp/bindat-tests.el bindat-test-unpack.  Reason:
;;; `bindat-pack' fills a `make-string' result with raw bytes
;;; (lisp/emacs-lisp/bindat.el:168, 585), and `bindat-unpack' signals
;;; "String is multibyte" on a multibyte argument (bindat.el:296).
;;; Vanilla Emacs calls that `make-string' result unibyte, so the guard
;;; stays quiet (doc/lispref/strings.texi:139-144).  Guilemacs keeps no
;;; unibyte string representation, so it can not copy vanilla Emacs.
;;; The checks below pin the raised behaviour.
(define mbsp
  (module-ref (resolve-module '(emacs strings)) 'elisp-multibyte-string-p))

;; Vanilla Emacs calls the literal "abc" multibyte and (make-string 3
;; ?a) unibyte (doc/lispref/nonascii.texi:165-169).  The predicate can
;; not tell the two apart, so it returns nil for both.
(check "m40/imp1/multibyte-string-p/ascii" #nil (mbsp "abc"))
(check "m40/imp1/multibyte-string-p/empty" #nil (mbsp ""))
(check "m40/imp1/multibyte-string-p/non-ascii" #nil (mbsp non-ascii))
;; A non-string returns nil, as in vanilla Emacs.
(check "m40/imp1/multibyte-string-p/number" #nil (mbsp 5))
(check "m40/imp1/multibyte-string-p/nil" #nil (mbsp #nil))
(check "m40/imp1/multibyte-string-p/symbol" #nil (mbsp 'foo))
;; An emacs-string wrapper follows the wrapper rule (unwrap, then test).
(check "m40/imp1/multibyte-string-p/wrapper-ascii" #nil
       (mbsp (make-emacs-string "abc")))
(check "m40/imp1/multibyte-string-p/wrapper-non-ascii" #nil
       (mbsp (make-emacs-string non-ascii)))
;; The byte-length probe is not the predicate.  It reports t for a
;; non-ASCII string, while the predicate reports nil.  Keep the probe, so
;; a later faithful port (a unibyte flag on strings) must change both
;; groups of checks together.
(define (byte-length-rule s)
  (if (> (elisp-string-bytes s) (string-length s)) #t #nil))
(check "m40/imp1/multibyte-string-p/byte-length-rule-ascii"
       #nil (byte-length-rule "abc"))
(check "m40/imp1/multibyte-string-p/byte-length-rule-non-ascii"
       #t (byte-length-rule non-ascii))

;;; --- 2. The buffer enable-multibyte-characters read ----------------
(define emc
  (module-ref (resolve-module '(emacs process-io))
              'object-enable-multibyte-characters))
(check "m40/imp1/buffer-read/defined" #t (procedure? emc))

;; The wrapper created and configured these buffers.
(define (get-buffer name) ((symbol-function 'get-buffer) name))
(define unibyte-buffer (get-buffer "m40-imp1-unibyte"))
(define multibyte-buffer (get-buffer "m40-imp1-multibyte"))
(check "m40/imp1/buffer-read/buffers-exist" #t
       (and (not (eq? unibyte-buffer #nil))
            (not (eq? multibyte-buffer #nil))))
;; The read is on the object buffer, not the current one.
(check "m40/imp1/buffer-read/unibyte" #nil (emc unibyte-buffer))
(check "m40/imp1/buffer-read/multibyte" #t (emc multibyte-buffer))
;; A non-buffer argument is defined and does not crash.
(check "m40/imp1/buffer-read/non-buffer" #nil (emc 5))

;;; --- 3. Static: the two modules carry the change --------------------
(define strings-src (slurp (repo "mod/emacs/strings.scm")))
;; cr.org F2: `contains?' gives #f for an absent file, so the negative
;; check below would pass when the file is unreadable.  Require the file
;; first, so an absent file is a real FAIL and not a silent pass.
(check "m40/imp1/static/strings-src-exists" #t (string? strings-src))
;; The deviation must be recorded in the module itself, not only in this
;; corpus.
(check "m40/imp1/static/strings-deviation-recorded" #t
       (contains? strings-src "FIX-20260921-guilemacs"))
;; The byte-length rule must not sit in the predicate body:
;; `bindat-unpack' signals on it.
(check "m40/imp1/static/strings-no-byte-length-rule" #f
       (contains? strings-src "(string->utf8 content)"))
;; brief.org §6.1: the predicate must be *exported* from the module, not
;; only defined.  The module-ref above proves the export at load time;
;; this static check names the export list, so a dropped export fails
;; with a clear message.
(define (export-block text)
  (and (string? text)
       (let ((start (string-contains text "#:export (")))
         (and start
              (let ((end (string-contains text "))" start)))
                (and end (substring text start end)))))))
(define strings-export-block (export-block strings-src))
(check "m40/imp1/static/strings-export-block-found" #t
       (string? strings-export-block))
(check "m40/imp1/static/strings-exports-predicate" #t
       (contains? strings-export-block "elisp-multibyte-string-p"))

(define pio-src (slurp (repo "mod/emacs/process-io.scm")))
(check "m40/imp1/static/helper-def" #t
       (contains? pio-src "(define (object-enable-multibyte-characters"))
;; cr.org F3: the old needle matched the `define' line only.  Assert the
;; body instead: it must call the elisp buffer-local-value path with the
;; object buffer as the argument, not the current buffer.
(check "m40/imp1/static/helper-takes-buffer" #t
       (and (contains? pio-src "(symbol-function 'buffer-local-value)")
            (contains? pio-src "'enable-multibyte-characters object)")))
(check "m40/imp1/static/helper-exported" #t
       (contains? pio-src "object-enable-multibyte-characters)"))

;;; --- 4. Static: the harness registers the M40 group -----------------
(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m40/imp1/run-tests/group-m40" #t
       (contains? run-tests "(group (m40)"))
(check "m40/imp1/run-tests/registers-imp1" #t
       (contains? run-tests "test/m40/test-m40-imp1.el"))
(check "m40/imp1/run-tests/registers-imp0" #t
       (contains? run-tests "test/m40/test-m40-imp0-audit.el"))
;; brief.org §6.3: the (m40) group sits *after* the (m39) group.
(check "m40/imp1/run-tests/group-m40-after-m39" #t
       (let ((i39 (and (string? run-tests)
                       (string-contains run-tests "(group (m39)")))
             (i40 (and (string? run-tests)
                       (string-contains run-tests "(group (m40)"))))
         (and i39 i40 (< i39 i40))))
