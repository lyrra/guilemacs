;;; test-m39-imp2.scm --- M39 imp-2: the process.c read/write decisions.
;;;
;;; brief.org (M39 imp-2) moves the decision logic of the process output
;;; path (src/process.c) into the module (emacs process-io):
;;;
;;;   send-process-state-decision   -- the send_process process-state
;;;                                    gate (pre-M39 body at :6790-6795).
;;;                                    It reads the process STATUS value
;;;                                    and the output fd OUTFD and owns
;;;                                    both tests.
;;;   process-send-region-gap-move? -- the GPT gap-move test of
;;;                                    Fprocess_send_region (:7033-7034).
;;;
;;; The mechanism stays C: the write loop, the coding setup, the buffer
;;; and string access.  The multibyte-versus-unibyte encoding branch of
;;; send_process stays C in this imp (the block-2 deviation; see
;;; mod/emacs/process-io.scm and docs/m39-plan.org §"Imp list").
;;;
;;; This corpus pins the port end state.  Two kinds of check:
;;;
;;;   - a runtime check: the module loads, exports the new procedures,
;;;     and each procedure computes the same decision as the pre-port C;
;;;   - a static wiring check: the old inline decision code is gone from
;;;     src/process.c, the C dispatchers are defined and called, the
;;;     mechanism stays C, the module is registered in prelude/load.scm,
;;;     and the region line pins match the tree.
;;;
;;; No check pins a forward declaration: the two imp-2 dispatchers sit
;;; above their callers in src/process.c, so the file needs none (brief.org
;;; Step 8 names one, but it is not needed here).
;;;
;;; The repo root is bound by the .el wrapper as %m39-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test
;;; and prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/m39/test-m39-imp2.el.

(use-modules (ice-9 rdelim))
(use-modules (srfi srfi-13))

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

(define (repo path) (string-append %m39-root "/" path))

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

(define (split-lines text)
  "Split TEXT on newlines."
  (if (not (string? text))
      '()
      (let loop ((start 0) (acc '()))
        (let ((idx (string-index text #\newline start)))
          (if (not idx)
              (reverse (cons (substring text start (string-length text)) acc))
              (loop (+ idx 1) (cons (substring text start idx) acc)))))))

(define (line-of text regexp)
  "1-based line number of the first line of TEXT that contains REGEXP
(as a plain substring), or #f."
  (let loop ((ls (split-lines text)) (n 1))
    (cond ((null? ls) #f)
          ((string-contains (car ls) regexp) n)
          (else (loop (cdr ls) (+ n 1))))))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m39-root))
    (begin (report "m39-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m39-root "."))
    (report "m39-root-bound" 'PASS))

;;; --- 1. The module loads and exports the new procedures ------------
(use-modules (emacs process-io))

(define %state-decision
  (module-ref (resolve-module '(emacs process-io))
              'send-process-state-decision))
(define %gap-move?
  (module-ref (resolve-module '(emacs process-io))
              'process-send-region-gap-move?))

(check "m39/imp2/export/send-process-state-decision" #t
       (and (defined? '%state-decision) (procedure? %state-decision)))
(check "m39/imp2/export/process-send-region-gap-move?" #t
       (and (defined? '%gap-move?) (procedure? %gap-move?)))

;;; --- 2. Runtime: the process-state gate, case by case --------------
;;; Each row is (status outfd) -> the code the pre-M39 C produced.  The
;;; module owns both tests now: not-running is STATUS not the symbol
;;; `run'; closed is OUTFD < 0.  The C order is kept: the not-running
;;; test fires before the closed-fd test.
(check "m39/imp2/runtime/state-ok" 0
       (%state-decision 'run 3))
(check "m39/imp2/runtime/state-not-running" 1
       (%state-decision 'exit 3))
(check "m39/imp2/runtime/state-not-running-wins" 1
       (%state-decision 'exit -1))
(check "m39/imp2/runtime/state-closed" 2
       (%state-decision 'run -1))
(check "m39/imp2/runtime/state-nil-status" 1
       (%state-decision #nil 3))

;;; --- 3. Runtime: the GPT gap-move predicate ------------------------
;;; The pre-M39 C test: XFIXNUM (start) < GPT && XFIXNUM (end) > GPT.
(check "m39/imp2/runtime/gap-move-inside" #t
       (%gap-move? 3 5 4))
(check "m39/imp2/runtime/gap-move-start-equal" #nil
       (%gap-move? 4 5 4))
(check "m39/imp2/runtime/gap-move-end-equal" #nil
       (%gap-move? 3 4 4))
(check "m39/imp2/runtime/gap-move-before" #nil
       (%gap-move? 1 2 10))
(check "m39/imp2/runtime/gap-move-after" #nil
       (%gap-move? 10 12 4))

;;; --- 4. Static: the module source defines and exports the procedures
(define pio (slurp (repo "mod/emacs/process-io.scm")))
(if (not pio)
    (report "m39/imp2/scan/module" (cons 'FAIL "mod/emacs/process-io.scm missing"))
    (begin
      (check "m39/imp2/module/defines-state-decision" #t
             (contains? pio "(define (send-process-state-decision"))
      (check "m39/imp2/module/defines-gap-move" #t
             (contains? pio "(define (process-send-region-gap-move?"))
      (check "m39/imp2/module/exports-state-decision" #t
             (contains? pio "send-process-state-decision\n            process-send-region-gap-move?"))
      ;; The state decision lives in the module: it tests STATUS and OUTFD.
      (check "m39/imp2/module/state-decides-status" #t
             (contains? pio "(not (eq? status 'run))"))
      (check "m39/imp2/module/state-decides-outfd" #t
             (contains? pio "(< outfd 0)"))
      ;; The module must not return a Scheme #f for a value C reads as a
      ;; number (the D2 #f trap); the state codes are integers.
      (check "m39/imp2/module/state-codes-integers" #t
             (contains? pio "%state-ok 0"))))

;;; --- 5. Static: src/process.c wires the dispatchers, old code is gone
(define proc-c (slurp (repo "src/process.c")))
(if (not proc-c)
    (report "m39/imp2/scan/process.c" (cons 'FAIL "src/process.c missing"))
    (begin
      ;; Both dispatchers are defined local to process.c.
      (check "m39/imp2/process.c/defines-state-dispatcher" #t
             (contains? proc-c "send_process_state_decision (Lisp_Object status, int outfd)"))
      (check "m39/imp2/process.c/defines-gap-move-dispatcher" #t
             (contains? proc-c "process_send_region_gap_move (EMACS_INT start"))
      ;; The public_ref module and symbol strings name this module.
      (check "m39/imp2/process.c/public-ref-module" #t
             (contains? proc-c "scm_c_public_ref (\"emacs process-io\""))
      (check "m39/imp2/process.c/public-ref-state" #t
             (contains? proc-c "\"send-process-state-decision\""))
      (check "m39/imp2/process.c/public-ref-gap-move" #t
             (contains? proc-c "\"process-send-region-gap-move?\""))
      ;; Both dispatchers are called by the reduced bodies.  The state
      ;; call passes the real status value and outfd, so the module owns
      ;; the decision (no C-side predicate).
      (check "m39/imp2/process.c/calls-state-dispatcher" #t
             (contains? proc-c "send_process_state_decision (p->status, p->outfd)"))
      (check "m39/imp2/process.c/calls-gap-move-dispatcher" #t
             (contains? proc-c "process_send_region_gap_move (XFIXNUM (start)"))
      ;; No C-side predicate survives before the state call.
      (check "m39/imp2/process.c/no-c-status-predicate" #f
             (contains? proc-c "EQ (p->status, Qrun) ? 1 : 0"))
      ;; The old inline decision code is gone.
      (check "m39/imp2/process.c/no-old-not-running-test" #f
             (contains? proc-c "if (! EQ (p->status, Qrun))"))
      (check "m39/imp2/process.c/no-old-closed-test" #f
             (contains? proc-c "if (p->outfd < 0)\n    error (\"Output file descriptor of %s is closed\", SDATA (p->name));"))
      (check "m39/imp2/process.c/no-old-gap-test" #f
             (contains? proc-c "XFIXNUM (start) < GPT && XFIXNUM (end) > GPT"))
      ;; The mechanism stays C.
      (check "m39/imp2/process.c/keeps-update-status" #t
             (contains? proc-c "if (p->raw_status_new)\n    update_status (p);"))
      (check "m39/imp2/process.c/keeps-move-gap" #t
             (contains? proc-c "move_gap_both (XFIXNUM (start), start_byte)"))
      (check "m39/imp2/process.c/keeps-char-to-byte" #t
             (contains? proc-c "start_byte = CHAR_TO_BYTE (XFIXNUM (start))"))
      (check "m39/imp2/process.c/keeps-write" #t
             (contains? proc-c "emacs_write_sig (outfd, cur_buf, cur_len)"))
      (check "m39/imp2/process.c/keeps-defun-region" #t
             (contains? proc-c "DEFUN (\"process-send-region\""))
      (check "m39/imp2/process.c/keeps-defun-string" #t
             (contains? proc-c "DEFUN (\"process-send-string\""))
      ;; The block-2 multibyte-versus-unibyte encoding branch stays C in
      ;; this imp.  The deviation is recorded in the module header and in
      ;; docs/m39-plan.org §"Imp list" (imp-2b).
      (check "m39/imp2/process.c/keeps-multibyte-branch" #t
             (contains? proc-c "STRINGP (object) && STRING_MULTIBYTE (object)"))
      ;; Line pins of the imp-2 region (measured at the write HEAD).
      (check "m39/imp2/process.c/pin-send-process" 6812
             (line-of proc-c "send_process (Lisp_Object proc, const char *buf"))
      (check "m39/imp2/process.c/pin-send-region" 7048
             (line-of proc-c "DEFUN (\"process-send-region\""))
      (check "m39/imp2/process.c/pin-send-string" 7087
             (line-of proc-c "DEFUN (\"process-send-string\""))))

;;; --- 6. Static: the module is registered with the prelude -----------
(define prelude (slurp (repo "prelude/load.scm")))
(check "m39/imp2/prelude/loads-process-io" #t
       (contains? prelude "(use-modules (emacs process-io))"))

;;; --- 7. Static: run-tests.scm registers the imp-2 corpus -----------
(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m39/imp2/run-tests.scm/registers-el" #t
       (contains? run-tests "test/m39/test-m39-imp2.el"))
