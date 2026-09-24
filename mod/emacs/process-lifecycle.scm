;;; process-lifecycle.scm --- M40 imp-4a: the process.c Group C
;;;                             small-gate decisions ((emacs process-lifecycle))
;;;
;;; Moves the *decision* of four src/process.c Group C names out of C and
;;; into Scheme.  The *mechanism* stays C: CHECK_PROCESS, the USHRT_MAX
;;; clamp and the set_window_size ioctl; the coding-system slot writes
;;; and setup_process_coding_systems; wait_for_socket_fds and the
;;; sockaddr conversions.  The C keeps each DEFUN and its elisp name;
;;; each DEFUN reads the decision with a small dispatcher
;;; (scm_c_public_ref + SCM_CALL_N), the shape of imp-2
;;; (send_process_object_multibyte_decision).
;;;
;;; Moved names, what the module owns, and what stays C:
;;;
;;;   set-process-window-size
;;;     owns: the NETCONN_P test and the infd < 0 test (the final
;;;           t/nil gate).  The C passes the NETCONN_P result, the input
;;;           fd, and the ioctl result.
;;;     keeps C: CHECK_PROCESS, the check_uinteger_max / USHRT_MAX
;;;           clamp, and the set_window_size ioctl.  The clamp stays C
;;;           because check_uinteger_max also signals the C argument
;;;           error, which a moved body cannot reproduce.
;;;
;;;   set-process-coding-system
;;;     owns: the Fcheck_coding_system order and the
;;;           infd < 0 || outfd < 0 early return (as an outcome code).
;;;     keeps C: the pset_* slot writes, coding_inherit_eol_type, and
;;;           setup_process_coding_systems.  coding_inherit_eol_type
;;;           stays C because it is a plain C function (src/coding.h),
;;;           not a subr, so Scheme cannot reach it.
;;;
;;;   process-datagram-address
;;;     owns: the nil result of the DATAGRAM_CONN_P gate.
;;;     keeps C: the DATAGRAM_CONN_P macro (it reads the C fd-keyed
;;;           datagram_address[] table), wait_for_socket_fds, and
;;;           conv_sockaddr_to_lisp.  The C computes the gate and passes
;;;           the result.
;;;
;;;   set-process-datagram-address
;;;     owns: the len == 0 || len != table-len gate.
;;;     keeps C: the DATAGRAM_CONN_P macro, get_lisp_to_sockaddr_size,
;;;           and conv_lisp_to_sockaddr.  The C passes len and the
;;;           table length.
;;;
;;; No live C DEFUN retires in this imp: each keeps its name and its
;;; mechanism, so process-contact's call to Fprocess_datagram_address
;;; stays valid.  No C fallback was added.
;;;
;;; Conventions (identical to M9-M40): #nil is elisp nil; no
;;; module-level mutable state.  Return an integer, not a Scheme #f, for
;;; any value C reads as a number: this Guile reads #f as elisp true.
;;; A decision that C reads as a boolean returns elisp #t / #nil.
;;;
;;; M40 imp-4b extends this module with the four remaining Group C
;;; decisions.  The shape is the same.  Each DEFUN stays C and keeps its
;;; elisp name; it reads the decision with a small dispatcher
;;; (scm_c_public_ref + SCM_CALL_N).  The C passes the facts that the
;;; module cannot compute (a C struct read, a C table read, the
;;; NETCONN1_P / SERIALCONN1_P / PIPECONN1_P macros, and the
;;; BUFFER_LIVE_P buffer-struct read).  See docs/kb.org ** M40.
;;;
;;;   delete-process
;;;     owns: the connection-kind branch selector (the outcome code).
;;;     keeps C: get_process, the Qmessage interactive test, the
;;;           HAVE_GETADDRINFO_A DNS block, pset_status, process_tick,
;;;           status_notify, redisplay_preserve_echo_area, the
;;;           alive / record_kill_process / kill path and the fd close.
;;;
;;;   process-send-eof
;;;     owns: the datagram early-return branch, and the alive gate.
;;;     keeps C: get_process, wait_while_connecting, the
;;;           proc_encode_coding_system lookup, the
;;;           CODING_REQUIRE_FLUSHING + send_process flush, the pty arm,
;;;           the serial arm (tcdrain) and the socket arm (shutdown,
;;;           close_process_fd, emacs_open (NULL_DEVICE ...),
;;;           setup_coding_system).  DATAGRAM_CONN_P stays C because it
;;;           reads the C fd-keyed datagram_address[] table; this repeats
;;;           the imp-4a deviation for process-datagram-address.
;;;
;;;   internal-default-process-filter
;;;     owns: the insert-or-discard gate (!NILP (p->buffer) &&
;;;           BUFFER_LIVE_P (XBUFFER (p->buffer))).  The C passes the
;;;           two booleans because BUFFER_LIVE_P reads the C buffer
;;;           struct.  The multibyteness-adjust gate stays C: it is not
;;;           thin (it reads the C string and buffer internals).
;;;     keeps C: read_process_output_before_insert, the multibyteness
;;;           adjust, insert_from_string_before_markers and
;;;           read_process_output_after_insert.
;;;
;;;   internal-default-process-sentinel
;;;     owns: the gate !EQ (symbol, Qrun) && !NILP (buffer) and the
;;;           inner BUFFER_LIVE_P gate (as one outcome code).  The C
;;;           passes symbol (p->status, its car when it is a cons), the
;;;           buffer-nonnil boolean and the buffer-live boolean.
;;;     keeps C: Fset_buffer, code_convert_string_norecord, the
;;;           point/marker bookkeeping, insert_string, Finsert,
;;;           set_marker_both and set_buffer_internal.
;;;
;;; No live C DEFUN retires in imp-4b: each keeps its name and its
;;; mechanism.  No C fallback was added.
;;;
;;; The durable record is docs/kb.org ** M40.

(define-module (emacs process-lifecycle)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (set-process-window-size-decision
            set-process-coding-system-decision
            process-datagram-address-decision
            set-process-datagram-address-decision
            delete-process-decision
            process-send-eof-datagram-decision
            process-send-eof-alive-decision
            internal-default-process-filter-decision
            internal-default-process-sentinel-decision))

;;; --- set-process-window-size --------------------------------------
;;; C body (src/process.c): return nil when NETCONN_P (process), or the
;;; input fd is negative, or the set_window_size ioctl failed; else t.
;;; The module owns the two tests and the result.  The C passes NETCONN
;;; (elisp t when NETCONN_P), INFD, and IOCTL-OK (elisp t when the ioctl
;;; succeeded; the C only runs the ioctl when NETCONN is nil and INFD is
;;; non-negative, so IOCTL-OK is nil in the other two cases).

(define (set-process-window-size-decision netconn infd ioctl-ok)
  "Return elisp t when PROCESS was told the window size, else elisp nil
(#nil).  NETCONN is elisp t when NETCONN_P (process); INFD is the input
file descriptor; IOCTL-OK is elisp t when the set_window_size ioctl
succeeded.  The gate is nil when NETCONN is t, or INFD is negative, or
the ioctl failed.  The C reads the result with NILP (a Scheme #f would
read as elisp true), so the body returns #t / #nil only."
  (if (or (eq? netconn #t)
          (< infd 0)
          (eq? ioctl-ok #nil))
      #nil
      #t))

;;; --- set-process-coding-system ------------------------------------
;;; C body (src/process.c): Fcheck_coding_system (decoding);
;;; Fcheck_coding_system (encoding); then (after the slot writes and
;;; coding_inherit_eol_type) return nil early when infd < 0 || outfd < 0,
;;; else run setup_process_coding_systems.  The module owns the check
;;; order and the early-return decision.  The C computes the outcome
;;; first (so the checks run before the slot writes, as in the original),
;;; acts on it after the writes.
;;
;;; Outcome codes: 0 proceed (run setup_process_coding_systems), 1 early
;;; return (return nil before setup).  The C reads the code with
;;; scm_to_int.

(define %coding-proceed 0)
(define %coding-skip 1)

(define (set-process-coding-system-decision decoding encoding infd outfd)
  "Run the two Fcheck_coding_system calls in the C order, then return an
integer outcome code: 0 when both fds are set up, 1 when infd or outfd
is negative (the C returns nil before setup_process_coding_systems).
The check calls reach the elisp `check-coding-system' subr.  The C keeps
the slot writes, coding_inherit_eol_type, and the final setup.

Returns an integer, not a Scheme #f, because the C reads it with
scm_to_int."
  ((symbol-function 'check-coding-system) decoding)
  ((symbol-function 'check-coding-system) encoding)
  (if (or (< infd 0) (< outfd 0)) %coding-skip %coding-proceed))

;;; --- process-datagram-address -------------------------------------
;;; C body (src/process.c): after wait_for_socket_fds, return nil unless
;;; DATAGRAM_CONN_P (process).  The gate reads the C datagram_address[]
;;; table, so the C computes it and passes the result.  The module owns
;;; the nil result.

(define (process-datagram-address-decision database)
  "Return elisp t when PROCESS is a datagram connection (DATABASE is
elisp t), else elisp nil (#nil).  The C computes DATAGRAM_CONN_P because
it reads the C fd-keyed datagram_address[] table; the module owns the
nil branch.  The C reads the result with NILP."
  (if (eq? database #t) #t #nil))

;;; --- set-process-datagram-address ---------------------------------
;;; C body (src/process.c): return nil when len == 0 or the table length
;;; differs from len.  The module owns that gate.  The C passes len and
;;; the table length as fixnums.
;;
;;; Outcome codes: 0 proceed (write the address), 1 return nil.  The C
;;; reads the code with scm_to_int.

(define %datagram-set-proceed 0)
(define %datagram-set-skip 1)

(define (set-process-datagram-address-decision len table-len)
  "Return an integer outcome code for the address-length gate of
set-process-datagram-address: 1 when LEN is zero or differs from
TABLE-LEN (the C returns nil), else 0 (the C writes the address).  LEN
and TABLE-LEN are exact integers.

Returns an integer, not a Scheme #f, because the C reads it with
scm_to_int."
  (if (or (= len 0) (not (= len table-len)))
      %datagram-set-skip
      %datagram-set-proceed))

;;; ----------------------------------------------------------------
;;; M40 imp-4b: the four remaining Group C decisions
;;; ----------------------------------------------------------------

;;; --- delete-process -----------------------------------------------
;;; C body (src/process.c): the branch selector
;;; NETCONN1_P (p) || SERIALCONN1_P (p) || PIPECONN1_P (p).  The C
;;; computes the three macros (they read the C struct) and passes one
;;; boolean.  The module owns the selector as an outcome code.  The C
;;; reads the code with scm_to_int.
;;;
;;; Outcome codes: 0 the status branch (pset_status + status_notify),
;;; 1 the kill branch (record_kill_process / the fd close).

(define %delete-process-status 0)
(define %delete-process-kill 1)

(define (delete-process-decision connection)
  "Return an integer outcome code for delete-process: 0 when PROCESS is
a network, serial or pipe connection (CONNECTION is elisp #t), so the C
runs the status branch; 1 otherwise, so the C runs the kill branch.  The
C computes NETCONN1_P (p) || SERIALCONN1_P (p) || PIPECONN1_P (p)
because the macros read the C struct; it passes elisp #t / #nil.

Returns an integer, not a Scheme #f, because the C reads it with
scm_to_int."
  (if (eq? connection #t) %delete-process-status %delete-process-kill))

;;; --- process-send-eof: the datagram early return ------------------
;;; C body (src/process.c): `if (DATAGRAM_CONN_P (proc)) return process;'.
;;; DATAGRAM_CONN_P reads the C fd-keyed datagram_address[] table, so the
;;; C computes the gate and passes it (elisp #t / #nil).  The module owns
;;; the branch.  The C reads the result with NILP.
;;;
;;; This repeats the imp-4a deviation for process-datagram-address: the
;;; macro stays C (a C table read).

(define (process-send-eof-datagram-decision datagram)
  "Return elisp t when PROC is a datagram connection (DATAGRAM is elisp
t), else elisp nil (#nil).  The C computes DATAGRAM_CONN_P because it
reads the C fd-keyed datagram_address[] table; the module owns the
branch.  The C reads the result with NILP (a Scheme #f would read as
elisp true), so the body returns #t / #nil only."
  (if (eq? datagram #t) #t #nil))

;;; --- process-send-eof: the alive gate -----------------------------
;;; C body (src/process.c): after update_status, `if (! EQ
;;; (XPROCESS (proc)->status, Qrun)) error (... not running ...);'.  The
;;; module owns the boolean (the process is alive when STATUS is the
;;; symbol `run').  The C passes the process STATUS value and keeps the
;;; error text and the name.  The C reads the result with NILP.

(define (process-send-eof-alive-decision status)
  "Return elisp t when the process is alive, else elisp nil (#nil).  The
process is alive when STATUS is the elisp symbol `run'.  The C refreshes
the status first (update_status, the mechanism) and passes STATUS; it
keeps the error text and the process name.  The C reads the result with
NILP (a Scheme #f would read as elisp true), so the body returns
#t / #nil only."
  (if (eq? status 'run) #t #nil))

;;; --- internal-default-process-filter ------------------------------
;;; C body (src/process.c): insert the output only when
;;; `!NILP (p->buffer) && BUFFER_LIVE_P (XBUFFER (p->buffer))'; else
;;; discard.  BUFFER_LIVE_P reads the C buffer struct, so the C computes
;;; both booleans and passes them (elisp #t / #nil each).  The module
;;; owns the gate.  The C reads the result with NILP.

(define (internal-default-process-filter-decision buffer-nonnil buffer-live)
  "Return elisp t when the filter must insert the output, else elisp nil
(#nil).  Insert when the process BUFFER-NONNIL is elisp t and
BUFFER-LIVE is elisp t (the C BUFFER_LIVE_P result).  The C computes the
two booleans because BUFFER_LIVE_P reads the C buffer struct; the module
owns the gate.  The C reads the result with NILP (a Scheme #f would read
as elisp true), so the body returns #t / #nil only."
  (if (and (eq? buffer-nonnil #t) (eq? buffer-live #t)) #t #nil))

;;; --- internal-default-process-sentinel ----------------------------
;;; C body (src/process.c): when `!EQ (symbol, Qrun) && !NILP (buffer)',
;;; then re-check `BUFFER_LIVE_P (XBUFFER (buffer))' and return nil for a
;;; dead buffer; else run the insert body.  SYMBOL is p->status (its car
;;; when it is a cons).  The C computes the car (a struct read) and the
;;; BUFFER_LIVE_P result (a buffer-struct read) and passes them.  The
;;; module owns both gates as one outcome code.  The C reads the code
;;; with scm_to_int.
;;;
;;; Outcome codes: 0 skip the whole block (the outer gate is false),
;;; 1 return nil for a dead buffer (the inner gate is false), 2 run the
;;; insert body.

(define %sentinel-skip 0)
(define %sentinel-dead-buffer 1)
(define %sentinel-insert 2)

(define (internal-default-process-sentinel-decision symbol buffer-nonnil
                                                   buffer-live)
  "Return an integer outcome code for the sentinel gate: 0 when SYMBOL is
the elisp symbol `run' or the process buffer is nil (BUFFER-NONNIL is
elisp #nil), so the C does nothing; 1 when the buffer is not live
(BUFFER-LIVE is elisp #nil), so the C returns nil; else 2, so the C runs
the insert body.  SYMBOL is the process STATUS value (its car when it is
a cons); the C computes it because it is a C struct read.

Returns an integer, not a Scheme #f, because the C reads it with
scm_to_int."
  (cond
    ((or (eq? symbol 'run) (eq? buffer-nonnil #nil)) %sentinel-skip)
    ((eq? buffer-live #nil) %sentinel-dead-buffer)
    (else %sentinel-insert)))
