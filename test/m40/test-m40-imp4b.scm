;;; test-m40-imp4b.scm --- M40 imp-4b: the remaining Group C decisions.
;;;
;;; brief.org (M40 imp-4b) moves the *decision* of four remaining
;;; src/process.c Group C names into the module (emacs process-lifecycle):
;;;
;;;   delete-process                    -- the connection-kind branch
;;;                                        selector (NETCONN1_P ||
;;;                                        SERIALCONN1_P || PIPECONN1_P),
;;;                                        as an outcome code.
;;;   process-send-eof                  -- the DATAGRAM_CONN_P early
;;;                                        return and the alive gate.
;;;   internal-default-process-filter   -- the insert-or-discard gate
;;;                                        (!NILP (p->buffer) &&
;;;                                        BUFFER_LIVE_P (XBUFFER (...))).
;;;   internal-default-process-sentinel -- the outer gate
;;;                                        (!EQ (symbol, Qrun) && !NILP
;;;                                        (buffer)) and the inner
;;;                                        BUFFER_LIVE_P gate, as one
;;;                                        outcome code.
;;;
;;; The mechanism stays C: get_process, the Qmessage test, the
;;; HAVE_GETADDRINFO_A DNS block, pset_status / status_notify /
;;; record_kill_process and the fd close; wait_while_connecting, the
;;; coding-system flush, the pty / serial / socket arms and the
;;; DATAGRAM_CONN_P table read; the insert machinery of the filter and
;;; the point/marker bookkeeping of the sentinel.  The C keeps each DEFUN
;;; and calls the module through a small dispatcher (scm_c_public_ref +
;;; SCM_CALL_N).  No C fallback was added.
;;;
;;; Two kinds of check: the decision value on synthetic inputs (the C
;;; rule, computed here independently of the module body spelling), and a
;;; static scan of the module, src/process.c, and the harness
;;; registration.
;;;
;;; The repo root is bound by the .el wrapper as %m40-root.  The .el
;;; wrapper also makes the live processes the e2e checks use (a pipe
;;; process); when a process cannot be made the e2e is INFO-skipped.  The
;;; .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test; see
;;; test/m40/test-m40-imp4b.el.  No datagram network process is used
;;; (brief.org section 4.2: it aborts Guile); the datagram gate is a unit
;;; check.

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

;;; --- 1. The module loads and exports the five procedures -----------
(define lifecycle (resolve-module '(emacs process-lifecycle)))
(define del (module-ref lifecycle 'delete-process-decision))
(define eof-dgram (module-ref lifecycle 'process-send-eof-datagram-decision))
(define eof-alive (module-ref lifecycle 'process-send-eof-alive-decision))
(define filt (module-ref lifecycle 'internal-default-process-filter-decision))
(define sent (module-ref lifecycle 'internal-default-process-sentinel-decision))

(check "m40/imp4b/export/delete-process-decision" #t (procedure? del))
(check "m40/imp4b/export/process-send-eof-datagram-decision" #t
       (procedure? eof-dgram))
(check "m40/imp4b/export/process-send-eof-alive-decision" #t
       (procedure? eof-alive))
(check "m40/imp4b/export/internal-default-process-filter-decision" #t
       (procedure? filt))
(check "m40/imp4b/export/internal-default-process-sentinel-decision" #t
       (procedure? sent))

;;; --- 2. Unit: the decision value on synthetic inputs ---------------
;;;
;;; The C rule of delete-process: run the status branch when NETCONN1_P
;;; || SERIALCONN1_P || PIPECONN1_P, else the kill branch.  The module
;;; returns 0 for the status branch and 1 for the kill branch.
(check "m40/imp4b/unit/delete/connection" 0 (del #t))
(check "m40/imp4b/unit/delete/not-connection" 1 (del #nil))

;;; The C rule of process-send-eof (the datagram early return): return
;;; the process when DATAGRAM_CONN_P.  The C passes the gate result.
(check "m40/imp4b/unit/eof-dgram/conn" #t (eof-dgram #t))
(check "m40/imp4b/unit/eof-dgram/not-conn" #nil (eof-dgram #nil))

;;; The C rule of process-send-eof (the alive gate): alive when the
;;; status is the symbol `run'.
(check "m40/imp4b/unit/eof-alive/run" #t (eof-alive 'run))
(check "m40/imp4b/unit/eof-alive/exit" #nil (eof-alive 'exit))
(check "m40/imp4b/unit/eof-alive/signal" #nil (eof-alive 'signal))
(check "m40/imp4b/unit/eof-alive/nil" #nil (eof-alive #nil))

;;; The C rule of internal-default-process-filter: insert when the
;;; buffer is non-nil AND live.
(check "m40/imp4b/unit/filter/insert" #t (filt #t #t))
(check "m40/imp4b/unit/filter/dead-buffer" #nil (filt #t #nil))
(check "m40/imp4b/unit/filter/no-buffer-live" #nil (filt #nil #t))
(check "m40/imp4b/unit/filter/no-buffer" #nil (filt #nil #nil))

;;; The C rule of internal-default-process-sentinel: 0 skip (symbol is
;;; `run', or the buffer is nil), 1 return nil (dead buffer), 2 insert.
(check "m40/imp4b/unit/sentinel/run" 0 (sent 'run #t #t))
(check "m40/imp4b/unit/sentinel/no-buffer" 0 (sent 'exit #nil #nil))
(check "m40/imp4b/unit/sentinel/dead-buffer" 1 (sent 'exit #t #nil))
(check "m40/imp4b/unit/sentinel/insert" 2 (sent 'exit #t #t))
;; The symbol is the process status; a run status skips even with a live
;; buffer (the outer gate fires first).
(check "m40/imp4b/unit/sentinel/run-live-buffer" 0 (sent 'run #t #t))

;;; --- 3. Runtime: the elisp names still resolve ---------------------
;;;
;;; The four DEFUNs stay C (they keep the mechanism), so the elisp names
;;; must still be subroutines.  The e2e calls live in the .el wrapper.
(for-each
 (lambda (name)
   (check (string-append "m40/imp4b/elisp/still-subr/" (symbol->string name)) #t
          (procedure? (symbol-function name))))
 '(delete-process process-send-eof internal-default-process-filter
   internal-default-process-sentinel))

;;; --- 4. Static: the module defines and exports the procedures -------
(define pl (slurp (repo "mod/emacs/process-lifecycle.scm")))
(check "m40/imp4b/static/module-src-exists" #t (string? pl))
(check "m40/imp4b/static/defines-delete" #t
       (contains? pl "(define (delete-process-decision connection)"))
(check "m40/imp4b/static/defines-eof-dgram" #t
       (contains? pl "(define (process-send-eof-datagram-decision datagram)"))
(check "m40/imp4b/static/defines-eof-alive" #t
       (contains? pl "(define (process-send-eof-alive-decision status)"))
(check "m40/imp4b/static/defines-filter" #t
       (contains? pl "(define (internal-default-process-filter-decision buffer-nonnil buffer-live)"))
(check "m40/imp4b/static/defines-sentinel" #t
       (contains? pl "(define (internal-default-process-sentinel-decision symbol buffer-nonnil"))
(check "m40/imp4b/static/exports-delete" #t
       (contains? pl "delete-process-decision"))
(check "m40/imp4b/static/exports-eof-dgram" #t
       (contains? pl "process-send-eof-datagram-decision"))
(check "m40/imp4b/static/exports-eof-alive" #t
       (contains? pl "process-send-eof-alive-decision"))
(check "m40/imp4b/static/exports-filter" #t
       (contains? pl "internal-default-process-filter-decision"))
(check "m40/imp4b/static/exports-sentinel" #t
       (contains? pl "internal-default-process-sentinel-decision"))
;; The module header records the moves and the names that stay C.
(check "m40/imp4b/static/header-records-move" #t
       (contains? pl "M40 imp-4b extends this module"))
(check "m40/imp4b/static/header-keeps-dns" #t
       (contains? pl "HAVE_GETADDRINFO_A DNS block"))
(check "m40/imp4b/static/header-keeps-dgram-macro" #t
       (contains? pl "datagram_address[] table"))
(check "m40/imp4b/static/header-keeps-marker" #t
       (contains? pl "set_marker_both"))
(check "m40/imp4b/static/header-no-fallback" #t
       (contains? pl "No C fallback was added."))
(check "m40/imp4b/static/cites-kb-m40" #t
       (contains? pl "docs/kb.org ** M40"))
;; Hygiene: no source comment cites the transient review file.
(define transient-review-needle (string-append "cr" ".org"))
(check "m40/imp4b/static/no-transient-cr-citation" #f
       (contains? pl transient-review-needle))

;;; --- 5. Static: src/process.c wiring and the kept DEFUNs ------------
(define proc-c (slurp (repo "src/process.c")))
(if (not proc-c)
    (report "m40/imp4b/scan/process.c" (cons 'FAIL "src/process.c missing"))
    (begin
      ;; The five dispatchers exist and ref the module.
      (check "m40/imp4b/process.c/dispatch-delete" #t
             (contains? proc-c "delete-process-decision\")"))
      (check "m40/imp4b/process.c/dispatch-eof-dgram" #t
             (contains? proc-c "process-send-eof-datagram-decision\")"))
      (check "m40/imp4b/process.c/dispatch-eof-alive" #t
             (contains? proc-c "process-send-eof-alive-decision\")"))
      (check "m40/imp4b/process.c/dispatch-filter" #t
             (contains? proc-c "internal-default-process-filter-decision\")"))
      (check "m40/imp4b/process.c/dispatch-sentinel" #t
             (contains? proc-c "internal-default-process-sentinel-decision\")"))
      (check "m40/imp4b/process.c/refs-lifecycle-module" #t
             (contains? proc-c "\"emacs process-lifecycle\""))
      ;; The DEFUNs stay C (they keep the mechanism).
      (check "m40/imp4b/process.c/keeps-defun-delete" #t
             (contains? proc-c "DEFUN (\"delete-process\""))
      (check "m40/imp4b/process.c/keeps-defun-eof" #t
             (contains? proc-c "DEFUN (\"process-send-eof\""))
      (check "m40/imp4b/process.c/keeps-defun-filter" #t
             (contains? proc-c "DEFUN (\"internal-default-process-filter\""))
      (check "m40/imp4b/process.c/keeps-defun-sentinel" #t
             (contains? proc-c "DEFUN (\"internal-default-process-sentinel\""))
      ;; The DEFUN bodies call the dispatchers (no C fallback).
      (check "m40/imp4b/process.c/calls-delete" #t
             (contains? proc-c "if (delete_process_decision (NETCONN1_P (p)"))
      (check "m40/imp4b/process.c/calls-eof-dgram" #t
             (contains? proc-c "if (process_send_eof_datagram_decision (DATAGRAM_CONN_P (proc)))"))
      (check "m40/imp4b/process.c/calls-eof-alive" #t
             (contains? proc-c "if (!process_send_eof_alive_decision (XPROCESS (proc)->status))"))
      (check "m40/imp4b/process.c/calls-filter" #t
             (contains? proc-c "internal_default_process_filter_decision (filter_buffer,"))
      (check "m40/imp4b/process.c/calls-sentinel" #t
             (contains? proc-c "internal_default_process_sentinel_decision"))
      ;; The C keeps the mechanism pieces.
      (check "m40/imp4b/process.c/keeps-dns" #t
             (contains? proc-c "#ifdef HAVE_GETADDRINFO_A"))
      (check "m40/imp4b/process.c/keeps-record-kill" #t
             (contains? proc-c "record_kill_process (p, Qnil)"))
      (check "m40/imp4b/process.c/keeps-remove-process" #t
             (contains? proc-c "remove_process (process)"))
      (check "m40/imp4b/process.c/keeps-wait-while-connecting" #t
             (contains? proc-c "wait_while_connecting (proc)"))
      (check "m40/imp4b/process.c/keeps-pty-eof" #t
             (contains? proc-c "send_process (proc, \"\\004\", 1, Qnil)"))
      (check "m40/imp4b/process.c/keeps-shutdown" #t
             (contains? proc-c "shutdown (old_outfd, 1)"))
      (check "m40/imp4b/process.c/keeps-null-device" #t
             (contains? proc-c "emacs_open (NULL_DEVICE, O_WRONLY, 0)"))
      (check "m40/imp4b/process.c/keeps-filter-insert" #t
             (contains? proc-c "insert_from_string_before_markers (text, 0, 0,"))
      (check "m40/imp4b/process.c/keeps-sentinel-marker" #t
             (contains? proc-c "set_marker_both (p->mark, p->buffer, PT, PT_BYTE)"))
      ;; The moved C-side predicates are gone from the DEFUN bodies.
      ;; (The delete-process selector string stays in Fprocess_status,
      ;; which the brief does not move; the calls-delete check above
      ;; proves the delete-process body uses the dispatcher.)
      (check "m40/imp4b/process.c/no-old-eof-alive" #f
             (contains? proc-c "if (! EQ (XPROCESS (proc)->status, Qrun))"))
      (check "m40/imp4b/process.c/no-old-sentinel-gate" #f
             (contains? proc-c "if (!EQ (symbol, Qrun) && !NILP (buffer))"))))

;;; --- 6. Static: the harness registers the M40 group -----------------
(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m40/imp4b/run-tests/registers-el" #t
       (contains? run-tests "test/m40/test-m40-imp4b.el"))

;;; --- 7. Static: the tree-wide scm_c_public_ref count ----------------
;;;
;;; imp-4b adds five scm_c_public_ref dispatcher sites in src/process.c,
;;; so the tree-wide count over src/*.c and src/*.h rises 167 -> 172.
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

(check "m40/imp4b/static/tree-ref-sites-258" 258 tree-ref-sites)

(define imp4b-corpus-src (slurp (repo "test/m40/test-m40-imp4b.scm")))
(check "m40/imp4b/static/corpus-no-transient-citation" #f
       (contains? imp4b-corpus-src transient-review-needle))
