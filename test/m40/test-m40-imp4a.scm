;;; test-m40-imp4a.scm --- M40 imp-4a: the Group C small-gate decisions.
;;;
;;; brief.org (M40 imp-4a) moves the *decision* of four src/process.c
;;; Group C names into the module (emacs process-lifecycle):
;;;
;;;   set-process-window-size        -- the NETCONN_P / infd < 0 / failed
;;;                                     ioctl gate.
;;;   set-process-coding-system      -- the Fcheck_coding_system order and
;;;                                     the infd < 0 || outfd < 0 early
;;;                                     return.
;;;   process-datagram-address       -- the DATAGRAM_CONN_P nil result.
;;;   set-process-datagram-address   -- the len == 0 || len != table-len
;;;                                     gate.
;;;
;;; The mechanism stays C: CHECK_PROCESS, the USHRT_MAX clamp and the
;;; set_window_size ioctl; the coding-system slot writes and
;;; setup_process_coding_systems; wait_for_socket_fds and the sockaddr
;;; conversions.  The C keeps each DEFUN and calls the module through a
;;; small dispatcher (scm_c_public_ref + SCM_CALL_N).  No C fallback was
;;; added.
;;;
;;; Two kinds of check: the decision value on synthetic inputs (the C
;;; rule, computed here independently of the module body spelling), and a
;;; static scan of the module, src/process.c, and the harness
;;; registration.
;;;
;;; The repo root is bound by the .el wrapper as %m40-root.  The .el
;;; wrapper also makes the live process the e2e checks use (a pipe
;;; process for window-size / coding-system); the datagram checks use
;;; synthetic inputs, not a datagram network process.  When a process
;;; cannot be made the e2e is INFO-skipped.  The .el wrapper turns each
;;; (NAME PASS|FAIL) pair into an ERT test; see test/m40/test-m40-imp4a.el.

(use-modules (srfi srfi-13))

(use-modules (emacs-elisp runtime))
(use-modules (emacs process-lifecycle))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (info name text)
  (report name (list 'INFO text)))

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

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m40-root))
    (begin (report "m40-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m40-root "."))
    (report "m40-root-bound" 'PASS))

;;; --- 1. The module loads and exports the four procedures -----------
(define lifecycle (resolve-module '(emacs process-lifecycle)))
(define win (module-ref lifecycle 'set-process-window-size-decision))
(define coding (module-ref lifecycle 'set-process-coding-system-decision))
(define dgram (module-ref lifecycle 'process-datagram-address-decision))
(define dgram-set (module-ref lifecycle 'set-process-datagram-address-decision))

(check "m40/imp4a/export/set-process-window-size-decision" #t
       (procedure? win))
(check "m40/imp4a/export/set-process-coding-system-decision" #t
       (procedure? coding))
(check "m40/imp4a/export/process-datagram-address-decision" #t
       (procedure? dgram))
(check "m40/imp4a/export/set-process-datagram-address-decision" #t
       (procedure? dgram-set))

;;; --- 2. Unit: the decision value on synthetic inputs ---------------
;;;
;;; The C rule of set-process-window-size (src/process.c):
;;;   nil when NETCONN_P, or infd < 0, or the set_window_size ioctl
;;;   failed; else t.  The C passes NETCONN (t/nil), INFD, and IOCTL-OK
;;;   (t/nil).
(check "m40/imp4a/unit/win/ok" #t (win #nil 5 #t))
(check "m40/imp4a/unit/win/netconn" #nil (win #t 5 #t))
(check "m40/imp4a/unit/win/negative-inf" #nil (win #nil -1 #t))
(check "m40/imp4a/unit/win/ioctl-failed" #nil (win #nil 5 #nil))

;;; The C rule of set-process-coding-system: check the two coding
;;; systems, then return nil early when infd < 0 || outfd < 0.  The
;;; module returns 0 to proceed, 1 to early return.
(check "m40/imp4a/unit/coding/ok" 0 (coding 'utf-8 'utf-8 5 6))
(check "m40/imp4a/unit/coding/negative-inf" 1 (coding 'utf-8 'utf-8 -1 6))
(check "m40/imp4a/unit/coding/negative-out" 1 (coding 'utf-8 'utf-8 5 -1))
;; An invalid coding system must still signal, as the C Fcheck_coding_system
;; did.  (The order is checked statically below.)
(check "m40/imp4a/unit/coding/invalid-signals" #t
       (catch #t (lambda () (coding 'not-a-coding-system 'utf-8 5 6) #f)
              (lambda args #t)))

;;; The C rule of process-datagram-address: return nil unless
;;; DATAGRAM_CONN_P.  The C passes the gate result.
(check "m40/imp4a/unit/dgram/conn" #t (dgram #t))
(check "m40/imp4a/unit/dgram/not-conn" #nil (dgram #nil))

;;; The C rule of set-process-datagram-address: return nil when len == 0
;;; or the table length differs from len.  0 proceed, 1 nil.
(check "m40/imp4a/unit/dgram-set/ok" 0 (dgram-set 16 16))
(check "m40/imp4a/unit/dgram-set/zero-len" 1 (dgram-set 0 16))
(check "m40/imp4a/unit/dgram-set/len-mismatch" 1 (dgram-set 16 8))

;;; --- 3. Runtime: the elisp names still resolve ---------------------
;;;
;;; The four DEFUNs stay C (they keep the mechanism), so the elisp names
;;; must still be subroutines.  The e2e calls live in the .el wrapper.
(for-each
 (lambda (name)
   (check (string-append "m40/imp4a/elisp/still-subr/" (symbol->string name)) #t
          (procedure? (symbol-function name))))
 '(set-process-window-size set-process-coding-system
   process-datagram-address set-process-datagram-address))

;;; --- 4. Static: the module defines and exports the procedures -------
(define pl (slurp (repo "mod/emacs/process-lifecycle.scm")))
(check "m40/imp4a/static/module-src-exists" #t (string? pl))
(check "m40/imp4a/static/defines-window-size" #t
       (contains? pl "(define (set-process-window-size-decision netconn infd ioctl-ok)"))
(check "m40/imp4a/static/defines-coding" #t
       (contains? pl "(define (set-process-coding-system-decision decoding encoding infd outfd)"))
(check "m40/imp4a/static/defines-dgram" #t
       (contains? pl "(define (process-datagram-address-decision database)"))
(check "m40/imp4a/static/defines-dgram-set" #t
       (contains? pl "(define (set-process-datagram-address-decision len table-len)"))
(check "m40/imp4a/static/exports-window-size" #t
       (contains? pl "set-process-window-size-decision"))
(check "m40/imp4a/static/exports-coding" #t
       (contains? pl "set-process-coding-system-decision"))
(check "m40/imp4a/static/exports-dgram" #t
       (contains? pl "process-datagram-address-decision"))
(check "m40/imp4a/static/exports-dgram-set" #t
       (contains? pl "set-process-datagram-address-decision"))
;; The coding decision reaches the elisp check-coding-system subr.
(check "m40/imp4a/static/coding-calls-check" #t
       (contains? pl "(symbol-function 'check-coding-system)"))
;; The module header records the moves and the names that stay C.
(check "m40/imp4a/static/header-records-move" #t
       (contains? pl "M40 imp-4a: the process.c Group C"))
(check "m40/imp4a/static/header-keeps-ioctl" #t
       (contains? pl "set_window_size ioctl"))
(check "m40/imp4a/static/header-keeps-eol" #t
       (contains? pl "coding_inherit_eol_type"))
(check "m40/imp4a/static/header-no-fallback" #t
       (contains? pl "No C fallback was added."))
(check "m40/imp4a/static/cites-kb-m40" #t
       (contains? pl "docs/kb.org ** M40"))
;; Hygiene: no source comment cites the transient review file.
(define transient-review-needle (string-append "cr" ".org"))
(check "m40/imp4a/static/no-transient-cr-citation" #f
       (contains? pl transient-review-needle))

;;; --- 5. Static: src/process.c wiring and the kept DEFUNs ------------
(define proc-c (slurp (repo "src/process.c")))
(if (not proc-c)
    (report "m40/imp4a/scan/process.c" (cons 'FAIL "src/process.c missing"))
    (begin
      ;; The four dispatchers exist and ref the module.
      (check "m40/imp4a/process.c/dispatch-window-size" #t
             (contains? proc-c "set-process-window-size-decision\")"))
      (check "m40/imp4a/process.c/dispatch-coding" #t
             (contains? proc-c "set-process-coding-system-decision\")"))
      (check "m40/imp4a/process.c/dispatch-dgram" #t
             (contains? proc-c "process-datagram-address-decision\")"))
      (check "m40/imp4a/process.c/dispatch-dgram-set" #t
             (contains? proc-c "set-process-datagram-address-decision\")"))
      (check "m40/imp4a/process.c/refs-lifecycle-module" #t
             (contains? proc-c "\"emacs process-lifecycle\""))
      ;; The DEFUNs stay C (they keep the mechanism).
      (check "m40/imp4a/process.c/keeps-defun-window-size" #t
             (contains? proc-c "DEFUN (\"set-process-window-size\""))
      (check "m40/imp4a/process.c/keeps-defun-coding" #t
             (contains? proc-c "DEFUN (\"set-process-coding-system\""))
      (check "m40/imp4a/process.c/keeps-defun-dgram" #t
             (contains? proc-c "DEFUN (\"process-datagram-address\""))
      (check "m40/imp4a/process.c/keeps-defun-dgram-set" #t
             (contains? proc-c "DEFUN (\"set-process-datagram-address\""))
      ;; The C keeps the mechanism pieces.
      (check "m40/imp4a/process.c/keeps-ioctl" #t
             (contains? proc-c "set_window_size (infd, h, w)"))
      (check "m40/imp4a/process.c/keeps-eol-call" #t
             (contains? proc-c "encoding = coding_inherit_eol_type (encoding, Qnil);"))
      (check "m40/imp4a/process.c/keeps-sockaddr" #t
             (contains? proc-c "conv_sockaddr_to_lisp"))))

;;; --- 6. Static: the harness registers the M40 group -----------------
(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m40/imp4a/run-tests/registers-el" #t
       (contains? run-tests "test/m40/test-m40-imp4a.el"))

;;; --- 7. Static: the tree-wide scm_c_public_ref count ----------------
;;;
;;; imp-4a adds four scm_c_public_ref dispatcher sites in src/process.c,
;;; so the tree-wide count over src/*.c and src/*.h rises 163 -> 167
;;; (and to 172 with the five imp-4b dispatchers).
(define (count-substr text sub)
  (if (not (string? text))
      0
      (let ((sl (string-length sub)))
        (let loop ((i 0) (n 0))
          (if (>= i (string-length text))
              n
              (let ((hit (string-contains text sub i)))
                (if hit (loop (+ hit sl) (1+ n)) n)))))))

(define (src-c-h-files)
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

(check "m40/imp4a/static/tree-ref-sites-177" 177 tree-ref-sites)

(define imp4a-corpus-src (slurp (repo "test/m40/test-m40-imp4a.scm")))
(check "m40/imp4a/static/corpus-no-transient-citation" #f
       (contains? imp4a-corpus-src transient-review-needle))
