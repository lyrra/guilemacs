;;; process-io.scm --- M39 imp-2: the process.c read/write decision paths
;;;                     ((emacs process-io))
;;;
;;; Moves the *decision* logic of the process output path out of C and
;;; into Scheme.  The *mechanism* stays C: the sendto/write syscall, the
;;; EINTR loop, the coding-system setup, the encode store loop, and the
;;; buffer and string access.  See docs/m39-plan.org §imp-2.
;;;
;;; Two M39 exported procedures:
;;;
;;;   send-process-state-decision   -- the send_process process-state
;;;                                    gate (src/process.c, pre-M39 body
;;;                                    at :6790-6795): not running, or
;;;                                    the output fd closed.  It reads
;;;                                    the process STATUS value and the
;;;                                    output fd OUTFD and owns the two
;;;                                    tests.
;;;   process-send-region-gap-move? -- the GPT gap-move test of
;;;                                    Fprocess_send_region
;;;                                    (src/process.c:7033-7034).
;;;
;;; Deviation from brief.org Step 3: the multibyte-versus-unibyte
;;; encoding branch of send_process (pre-M39 :6790-6843, the largest
;;; decision of the region) stays C in this imp.  Its predicate is
;;; `(STRINGP (object) && STRING_MULTIBYTE (object))
;;;  || (BUFFERP (object) && enable-multibyte-characters) || EQ (object, Qt)'.
;;; A faithful Scheme port needs a Scheme-side STRING_MULTIBYTE and a
;;; Scheme-side buffer enable-multibyte-characters read.  In this build
;;; multibyte-string-p is a stub (mod/emacs/strings.scm elisp-multibyte-
;;; string-p returns nil always), while the C STRING_MULTIBYTE is a real
;;; test (src/lisp.h:1199-1206).  Moving the branch now would need a new
;;; C shim or a behavior change on the send path -- against the "no C
;;; fallback" rule.  The rule of `:6819` (NETCONN_P -> wait_while_connecting)
;;; also stays C, because brief.org Step 3 names wait_while_connecting a
;;; mechanism.  A follow-up imp ports both.  See docs/m39-plan.org
;;; §"Imp list" (imp-2b) and docs/kb.org ** M39.
;;;
;;; The C keeps the mechanism the recipe names: update_status, error,
;;; CHAR_TO_BYTE, move_gap_both, BYTE_POS_ADDR, get_process, SSDATA,
;;; setup_coding_system, complement_process_encoding_system, and the
;;; write loop.
;;;
;;; Conventions (identical to M9-M39): defelisp delayed references for
;;; every C DEFUN ((force %--foo)); #nil is elisp nil; no module-level
;;; mutable state.  Return integers, not a Scheme #f, for any value C
;;; reads as a number: this Guile reads #f as elisp true.

(define-module (emacs process-io)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (send-process-state-decision
            process-send-region-gap-move?))

;; Outcome codes of send-process-state-decision.  The C caller
;; (src/process.c send_process_state_decision) reads the result with
;; scm_to_int and signals the matching error.
(define %state-ok 0)
(define %state-not-running 1)
(define %state-closed 2)

(define (send-process-state-decision status outfd)
  "Port of the send_process process-state gate
(src/process.c:6790-6795, pre-M39).  The C caller refreshes the status
first (update_status, the mechanism) and passes the process STATUS value
and the output file descriptor OUTFD.  The decision lives here: the
process is not running when STATUS is not the symbol `run'; the output
fd is closed when OUTFD is negative.  Returns an integer code: 0 ok,
1 process not running, 2 output fd closed.  The C signals the error
message for the code.  The C order is kept: the not-running test fires
before the closed-fd test.

Returns integers, not a Scheme #f, so no false value can read as elisp
true (#f is not #nil)."
  (cond
    ((not (eq? status 'run)) %state-not-running)
    ((< outfd 0) %state-closed)
    (else %state-ok)))

(define (process-send-region-gap-move? start end gpt)
  "Port of the gap-move test of Fprocess_send_region
(src/process.c:7033-7034, pre-M39): move the buffer gap when START is
before GPT and END is after it.  START and END are character positions;
GPT is the gap position.  Returns elisp t, else elisp nil (#nil).  The C
caller keeps CHAR_TO_BYTE, move_gap_both, and the byte addresses; the
dispatcher reads the result with NILP."
  (if (and (< start gpt) (> end gpt))
      #t
      #nil))
