;;; tty-output.scm --- M52 imp-3: the src/term.c TTY output boundary
;;;                     ((emacs tty-output))
;;;
;;; M52 imp-3 defines the boundary of the src/term.c TTY output path.
;;; It moves NO policy: the selection of the capability string and the
;;; cursor / scroll / clear arithmetic stay in C until imp-4.  This
;;; module holds the 4 thin wrappers over the 4 typed C leaves only.
;;;
;;; The C leaves (src/term.c):
;;;
;;;   (%--tty-emit-cap   device cap args) -> a fixnum byte count, or a
;;;        negative fixnum holding the negated errno
;;;   (%--tty-write-bytes device bytevector) -> the same shape
;;;   (%--tty-flush       device)          -> 0, or a negated errno
;;;   (%--tty-emit-seq    device seq)      -> the total byte count
;;;
;;; Every value that crosses the layer is plain: the DEVICE is an opaque
;;; handle (a terminal object, a frame, or nil), the CAP key is a plain
;;; string, the ARGS is a plain fixnum list, and the SEQ is a plain list
;;; of (cap . args) items.  No Lisp_Object, char *, FILE *, or struct
;;; crosses the layer (the M42 rule).  The C-owned FILE *output and
;;; FILE *termscript streams stay in C; C stays the single writer.  A
;;; Guile port must NOT own a C-owned FILE * stream (docs/kb.org
;;; =passthrough-leaf-is-not-a-port=).
;;;
;;; The module is a NEW module.  The sibling (emacs terminal) owns the
;;; M48 display queries and the M33 menu consumers, and (emacs tty-modes)
;;; owns the termios mode policy in src/sysdep.c.  A new module does not
;;; extend a sibling.  It holds no policy, no FFI call, and no public
;;; ref site yet (the FFI bridge comes at imp-4).
;;;
;;; The cleanup contract (brief.org section 6, the leaf rules) is a leaf
;;; property:
;;;   - A SHORT WRITE: the C leaf reports the fwrite count to Scheme, so
;;;     Scheme decides retry / give-up.  C keeps the =clearerr=.
;;;   - EINTR / EAGAIN: the fwrite path does not handle them today; the
;;;     tcdrain drain retries EINTR (src/sysdep.c).  A leaf returns the
;;;     negated errno on a hard failure.
;;;   - EOF: not applicable to output.
;;;   - CLOSE: C closes the streams.  Scheme never closes them.
;;;
;;; The padding note (cr1.org F3, for imp-4): the real termcap output
;;; path is the C OUTPUT macro, which calls emacs_tputs and applies
;;; padding.  The leaf m52_tty_emit_cap_1 calls tparam and a raw
;;; fwrite, so it does NOT apply padding.  imp-3 rewires nothing, so
;;; there is no regression today.  When imp-4 moves the output policy,
;;; it MUST NOT lose the padding behaviour: either call emacs_tputs, or
;;; record the padding decision in docs/m52-plan.org.
;;;
;;; Conventions (identical to M9-M51): defelisp delayed references for
;;; every C DEFUN ((force %--foo)); elisp nil is #nil; no module-level
;;; mutable state.

(define-module (emacs tty-output)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (tty-emit-cap tty-write-bytes tty-flush tty-emit-seq
            tty-turn-on-insert-cap tty-turn-off-insert-cap
            tty-turn-off-highlight-cap tty-turn-on-highlight-cap
            tty-toggle-highlight-cap))

;; The typed C leaves of src/term.c.
(defelisp %--tty-emit-cap   --tty-emit-cap)
(defelisp %--tty-write-bytes --tty-write-bytes)
(defelisp %--tty-flush      --tty-flush)
(defelisp %--tty-emit-seq   --tty-emit-seq)

;; Emit one termcap capability of DEVICE.  DEVICE is an opaque handle;
;; CAP is a plain string naming one TS_* capability; ARGS is a plain
;; fixnum list applied through tparam.  Return the leaf's plain fixnum:
;; the byte count, or a negative fixnum holding the negated errno.
(define (tty-emit-cap device cap args)
  ((force %--tty-emit-cap) device cap args))

;; Write the plain bytevector BYTES to DEVICE's output and termscript
;; streams (the bell / newline path).  Return the leaf's plain fixnum:
;; the byte count, or a negated errno.
(define (tty-write-bytes device bytes)
  ((force %--tty-write-bytes) device bytes))

;; Flush the C-owned output stream of DEVICE.  Return the leaf's plain
;; fixnum: 0 on success, or a negated errno.
(define (tty-flush device)
  ((force %--tty-flush) device))

;; Apply one ordered sequence SEQ of (CAP . ARGS) items to DEVICE.  This
;; is the thin entry point; it adds no policy.  Return the leaf's plain
;; fixnum: the total byte count, or a negated errno.
(define (tty-emit-seq device seq)
  ((force %--tty-emit-seq) device seq))

;; --- M52 imp-4: the insert / highlight state-flip policy --------------
;;
;; Each procedure holds the DECISION of one src/term.c hub: given the
;; plain C state flag (a fixnum, 0 or 1) it returns the plain capability
;; KEY string to emit, or #nil when the hub must emit nothing.  The
;; selection is pure: a procedure calls no leaf and emits nothing
;; (docs/kb.org =leaf-must-call-the-mechanism=).  Each returned key MUST
;; match a m52_caps key byte for byte; a key that does not match makes
;; m52_cap_string_1 return NULL, so the hub emits nothing (a silent byte
;; change).  C owns the state write and the OUTPUT / OUTPUT_IF call.

;; tty_turn_on_insert: emit only when insert-mode is off.
(define (tty-turn-on-insert-cap insert-mode)
  (if (zero? insert-mode) "insert-mode" #nil))

;; tty_turn_off_insert: emit only when insert-mode is on.
(define (tty-turn-off-insert-cap insert-mode)
  (if (zero? insert-mode) #nil "end-insert-mode"))

;; tty_turn_off_highlight: emit only when standout-mode is on.
(define (tty-turn-off-highlight-cap standout-mode)
  (if (zero? standout-mode) #nil "end-standout-mode"))

;; tty_turn_on_highlight: emit only when standout-mode is off.
(define (tty-turn-on-highlight-cap standout-mode)
  (if (zero? standout-mode) "standout-mode" #nil))

;; tty_toggle_highlight: the two-way flip.  Choose the direction from the
;; plain flag and return that direction's key (never #nil).
(define (tty-toggle-highlight-cap standout-mode)
  (if (zero? standout-mode) "standout-mode" "end-standout-mode"))
