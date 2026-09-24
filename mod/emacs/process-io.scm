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
;;; M40 imp-2 moves the multibyte-versus-unibyte *decision* of
;;; send_process (src/process.c, the previous predicate at :6843-6846)
;;; into this module as send-process-object-multibyte?.  Its predicate is
;;; `(STRINGP (object) && STRING_MULTIBYTE (object))
;;;  || (BUFFERP (object) && enable-multibyte-characters) || EQ (object, Qt)'.
;;; Two imp-2 exports supply the terms:
;;;
;;;   process-string-needs-encoding? -- the STRINGP + STRING_MULTIBYTE
;;;                                     term, under a *process-local*
;;;                                     name.  It answers the C question
;;;                                     ("does this string need
;;;                                     encoding"), not the elisp-visible
;;;                                     question.  The elisp name
;;;                                     multibyte-string-p stays nil.
;;;   send-process-object-multibyte? -- the whole if-condition.  It ORs
;;;                                     the string term, the imp-1 buffer
;;;                                     term (object-enable-multibyte-characters),
;;;                                     and the Qt term.
;;;
;;; The string term uses the C STRING_MULTIBYTE rule (src/lisp.h:1196-1207):
;;; a string is multibyte when its UTF-8 byte length differs from its
;;; character length.  Guilemacs keeps no unibyte string representation, so
;;; the elisp multibyte-string-p stays nil and this process-local helper
;;; mirrors the C byte-length rule instead.  A faithful multibyte-string-p
;;; needs a shared unibyte flag on strings, a separate candidate task.
;;; See docs/m40-plan.org §3.1 and docs/kb.org ** M40.
;;;
;;; The two arms (the coding-system setup, complement_process_encoding_system,
;;; the raw-text fallback, the byte-position code) and the rule of
;;; `:6841-6845` (NETCONN_P -> wait_while_connecting) stay C.  brief.org
;;; Step 3 names wait_while_connecting a mechanism.
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
  #:use-module (rnrs bytevectors)     ; string->utf8, bytevector-length
  #:use-module (emacs text-properties) ; emacs-string?, emacs-string-content
  #:declarative? #t
  #:export (send-process-state-decision
            process-send-region-gap-move?
            process-string-needs-encoding?
            send-process-object-multibyte?
            object-enable-multibyte-characters))

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

;;; ----------------------------------------------------------------
;;; M40 imp-1: the buffer enable-multibyte-characters read
;;; ----------------------------------------------------------------
;;;
;;; The send_process branch (imp-2) tests
;;; `BUFFERP (object) && !NILP (BVAR (XBUFFER (object),
;;; enable_multibyte_characters))'.  The read is on the *object* buffer,
;;; not on the current buffer, so the helper takes a buffer argument.
;;; It reuses the existing elisp `buffer-local-value' path (brief.org
;;; M40 imp-1 §5.2 option 1) and adds no C.  `enable-multibyte-characters'
;;; is DEFVAR_PER_BUFFER (src/buffer.c:5206); buffer-local-value reads it
;;; from the per-buffer hash by its Lisp symbol.

(define (object-enable-multibyte-characters object)
  "Return elisp t when the buffer OBJECT has `enable-multibyte-characters'
non-nil, else elisp nil (#nil).  The variable is read on OBJECT itself,
not on the current buffer, because the C branch tests XBUFFER (object).
A non-buffer OBJECT returns nil.  The result is forced to a boolean so a
Scheme #f can never leak and read as elisp true."
  (if (eq? ((symbol-function 'bufferp) object) #nil)
      #nil
      (if (eq? ((symbol-function 'buffer-local-value)
                'enable-multibyte-characters object)
               #nil)
          #nil
          #t)))

;;; ----------------------------------------------------------------
;;; M40 imp-2: the send_process multibyte-versus-unibyte decision
;;; ----------------------------------------------------------------
;;;
;;; The branch predicate of send_process:
;;; `(STRINGP (object) && STRING_MULTIBYTE (object))
;;;  || (BUFFERP (object) && enable-multibyte-characters) || EQ (object, Qt)'.
;;; The three terms map to: process-string-needs-encoding?,
;;; object-enable-multibyte-characters (imp-1), and the Qt test.

(define (process-string-needs-encoding? object)
  "Return elisp t when OBJECT is a string whose C STRING_MULTIBYTE test
is true, else elisp nil (#nil).  This is the STRINGP + STRING_MULTIBYTE
term of the send_process decision, under a *process-local* name.

The rule is the C one (src/lisp.h:1196-1207): a string is multibyte when
its UTF-8 byte length differs from its character length.  A non-string
OBJECT returns nil, so the caller may pass any object (the C tests
STRINGP first).

Do NOT confuse this name with the elisp `multibyte-string-p': that name
stays nil (mod/emacs/strings.scm, FIX-20260921-guilemacs), because a
faithful answer needs a unibyte flag on strings and the byte-length rule
breaks bindat-unpack.  This helper answers the process question only.
See docs/m40-plan.org §3.1.

The STRINGP test accepts both a plain Guile string and an emacs-string
wrapper (a text-property string).  It does NOT use the elisp `stringp':
that predicate is broken for text-property strings (see docs/kb.org
Gotcha stringp-false-for-text-property-strings).  The wrapper content is
unwrapped before the byte count, so a propertized string reads the same
as a plain one."
  (cond
    ((string? object)
     (if (not (= (bytevector-length (string->utf8 object))
                 (string-length object)))
         #t
         #nil))
    ((emacs-string? object)
     (let ((content (emacs-string-content object)))
       (if (not (= (bytevector-length (string->utf8 content))
                   (string-length content)))
           #t
           #nil)))
    (else #nil)))

(define (send-process-object-multibyte? object)
  "Return elisp t when the send_process multibyte arm runs for OBJECT,
else elisp nil (#nil).  This is the whole if-condition of the C:

  (STRINGP (object) && STRING_MULTIBYTE (object))
  || (BUFFERP (object) && enable-multibyte-characters)
  || EQ (object, Qt)

The three terms: process-string-needs-encoding?, the imp-1 buffer
predicate object-enable-multibyte-characters, and the Qt test.  The C
caller (src/process.c send_process_object_multibyte_decision) reads the
result with !NILP.  The result is forced to a boolean, so a Scheme #f
can never leak and read as elisp true.

The Qt term mirrors the C EQ (object, Qt).  In this tree Qt is
SCM_BOOL_T (src/lread.c:2878), so Qt reaches Scheme as #t.  The Guile
symbol t is NOT Qt: the C EQ (object, Qt) is false for it, so this
predicate returns #nil for the symbol t (docs/kb.org ** M40)."
  (if (or (eq? (process-string-needs-encoding? object) #t)
          (eq? (object-enable-multibyte-characters object) #t)
          (eq? object #t))
      #t
      #nil))
