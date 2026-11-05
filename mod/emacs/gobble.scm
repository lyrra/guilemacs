;;; gobble.scm --- M25 imp-1 + imp-2 + imp-3 + imp-4: user-signal
;;;                  drain, async input, gobble_input terminal walk,
;;;                  tty_read_avail_input byte read/decode
;;;                  ((emacs gobble))
;;;
;;; Moves the normal-context *policy* for user-signal drain, the
;;; async-input/pending-signals dispatch, and the gobble_input
;;; terminal-list walk out of src/keyboard.c and into Scheme.  The raw
;;; C data stays C (see per-imp notes):
;;;
;;; imp-1 (store-user-signal-events!):
;;;   - store-user-signal-events!  per-signal drain loop: for each
;;;                             registered signal with pending events,
;;;                             store one USER_SIGNAL_EVENT per pending
;;;                             count and reset it to zero.  The raw C
;;;                             user_signals list stays C because
;;;                             handle_user_signal touches it from a
;;;                             signal handler.
;;;
;;; imp-2 (handle-async-input! / process-pending-signals!):
;;;   - handle-async-input!      drain the input queue: call
;;;                             --gobble-input until it reports no more
;;;                             input (0) or a blocked read (< 0).
;;;   - process-pending-signals! clear the pending-signals flag, then
;;;                             handle-async-input!, then run due
;;;                             atimers.  Order matches the C original.
;;;
;;; imp-3 (gobble-input!):
;;;   - gobble-input!             walk the terminal list newest-first,
;;;                             drain each terminal's read_socket_hook
;;;                             (a raw C function pointer, so the drain
;;;                             call stays a shim) until it reports
;;;                             <= 0, then make every affected frame's
;;;                             pointer visible and store any quit
;;;                             event the drain left in hold_quit.
;;;                             The nr == -2 terminal-death arm (delete
;;;                             the terminal, or SIGHUP-terminate if it
;;;                             was the last one) stays inside the drain
;;;                             shim, in C: terminate_due_to_signal
;;;                             never returns, so it must not unwind
;;;                             through a live Scheme call frame.
;;;
;;; C entry points that are now thin dispatchers into this module:
;;; handle_async_input and process_pending_signals (imp-2) and
;;; gobble_input (imp-3).  store_user_signal_events (imp-1) was
;;; deleted, not retained: gobble-input! calls store-user-signal-events!
;;; directly (see brief.org M25 imp-3 Cleanup).  Unlike add_user_signal
;;; (imp-1), none of these entry points has an early-init caller: all
;;; callers run during normal command-loop or wait-loop execution, so a
;;; Scheme dispatch is safe there (see
;;; early-init-c-body-before-defun-registration, docs/kb.org).
;;; add_user_signal stays a C body: init_signals calls it before
;;; syms_of_keyboard registers the --user-signal-* DEFUNs.  See brief.org
;;; M25 imp-1, imp-2 and imp-3 and their close-outs.
;;;
;;; Conventions (identical to M9-M24): defelisp delayed references for
;;; every C DEFUN ((force %--foo)); elisp nil is #nil.  Every call
;;; re-reads the C state fresh through the shims — no module-level
;;; mutable cache (unlike (emacs input-poll)).  kbd-buffer-store-event!
;;; lives in (emacs kbd-buffer) but that module is resolved lazily (a
;;; delayed module-ref), never imported eagerly: an eager #:use-module
;;; would make gobble.scm depend on the whole kbd-buffer import chain
;;; (lispy-event -> lispy-position), which fails at prelude time when
;;; lispy-position is not yet loaded — the same idiom
;;; read-key-sequence.scm uses for kbd-buffer-readable-events.

(define-module (emacs gobble)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:use-module (rnrs bytevectors)     ; bytevector-u8-ref (tty byte decode)
  #:use-module ((emacs event-modifiers) #:select (meta-modifier))
  #:declarative? #t
  #:export (store-user-signal-events!
            handle-async-input!
            process-pending-signals!
            gobble-input!
            tty-read-avail-input!
            input-handle-id input-handle-state
            input-handle-open! input-handle-close!
            prime-input-handle!))

(defelisp %--user-signal-list               --user-signal-list)
(defelisp %--user-signal-pending            --user-signal-pending)
(defelisp %--user-signal-pending-decrement! --user-signal-pending-decrement!)
(defelisp %--ie-user-signal-event           --ie-user-signal-event)

;; imp-2 shims: --gobble-input (reused, also defelisp'd by kbd-buffer.scm
;; and read-key-sequence.scm under their own local names) plus the two new
;; single-purpose triggers for the C cells that must stay C.
(defelisp %--gobble-input           --gobble-input)
(defelisp %--pending-signals-clear! --pending-signals-clear!)
(defelisp %--do-pending-atimers!    --do-pending-atimers!)

;; imp-3 shims and helpers.  The terminal/frame walk uses the existing
;; elisp primitives terminal-list / frame-list / frame-terminal; a
;; terminal object is a pseudovector, so terminals compare with eq?.
;; The four single-purpose shims wrap the C bits that must stay C: the
;; read_socket_hook call and the nr == -2 death arm (--terminal-read-
;; socket-hook!, which may terminate_due_to_signal), pending_signals
;; (--pending-signals-set!, also written by a signal handler), and
;; frame_make_pointer_visible (--frame-make-pointer-visible!).
;; --input-blocked-p already existed.  --ie-kind reads a drain shim's
;; returned ie-smob; NO_EVENT is event_kind 0.
(defelisp %terminal-list                 terminal-list)
(defelisp %frame-list                    frame-list)
(defelisp %frame-terminal                frame-terminal)
(defelisp %--input-blocked-p             --input-blocked-p)
(defelisp %--terminal-read-socket-hook-p --terminal-read-socket-hook-p)
(defelisp %--terminal-read-socket-hook!  --terminal-read-socket-hook!)
(defelisp %--pending-signals-set!        --pending-signals-set!)
(defelisp %--frame-make-pointer-visible! --frame-make-pointer-visible!)
(defelisp %--ie-kind                     --ie-kind)

;; imp-4 shims and helpers.  tty-read-avail-input! reads the terminal's
;; byte source and per-terminal meta/top-frame state through these
;; single-purpose shims, whose C bodies own the USABLE_FIONREAD sizing,
;; the nonblocking emacs_read (with its EIO close-terminal arm), and the
;; raw meta_key / top_frame fields.  --quit-char, --kbd-on-hold-p and
;; --kbd-buffer-nr-stored are reused (kbd-buffer.scm also defelisp's the
;; same C primitives under its own local names — the established
;; pattern).  kbd-buffer-store-event! is the shared M13 store.
(defelisp %--kbd-buffer-nr-stored        --kbd-buffer-nr-stored)
(defelisp %--kbd-on-hold-p               --kbd-on-hold-p)
(defelisp %--quit-char                   --quit-char)
(defelisp %--tty-meta-key                --tty-meta-key)
(defelisp %--tty-top-frame               --tty-top-frame)
(defelisp %--tty-bytes-readable          --tty-bytes-readable)
(defelisp %--tty-read-nonblocking        --tty-read-nonblocking)
(defelisp %--ie-ascii-keystroke-event    --ie-ascii-keystroke-event)

;; M63 imp-2 (the opaque INPUT handle): the 3 leaves take the PLAIN
;; identity that --tty-handle already answers.  The handle BORROWS that
;; identity; Scheme holds the state and the byte count, C keeps the
;; descriptor, the readiness registration, the read leaf and the event
;; ring.  No descriptor, no FILE * and no struct tty_display_info *
;; crosses: the identity is the only value on the seam.
(defelisp %--tty-handle              --tty-handle)
(defelisp %--m63-input-state         --m63-input-state)
(defelisp %--m63-input-open!         --m63-input-open!)
(defelisp %--m63-input-close!        --m63-input-close!)

;; The 3 states of the handle.  C keeps the storage word; the values are
;; the same 3 numbers on both sides of the seam.
;;
;; READER NOTE (review cr.org F8): only +input-closed+ has a production
;; reader.  +input-borrowed+ and +input-open+ have no production reader:
;; they name the states that the read path WRITES but does not test.
;; The state machine has 1 observable production transition: the read
;; body writes +input-open+ on a positive count.  No production caller
;; runs input-handle-close!.  That is expected for a BORROWED handle:
;; this act builds the seam that imp-3 and imp-4 use.
;; Protection of the 2 copies (the C macros M63_INPUT_* and these
;; constants): the PTY case m63-imp2/closed-e2e reads the state word
;; through input-handle-state and pins CLOSED = 2, so a mismatch of
;; +input-closed+ fails that case.  A mismatch of +input-borrowed+ or
;; +input-open+ fails no test.  Do not add a test that pins the pair
;; against the C macros (brief.org section 10, limit 3).
(define +input-borrowed+ 0)
(define +input-open+     1)
(define +input-closed+   2)

;; The "no identity" bound of the RESOLVE step.  It is NOT a state: 0
;; from the bootstrap leaf means "the tty holds no identity yet", while
;; the state words of the table are also 0, 1 and 2.  The 2 names stay
;; apart, so a later change of a state value can not move the identity
;; bound.
(define +no-identity+ 0)

;; The ONE Scheme definition of EBADF is tty-handle-ebadf in
;; (emacs tty-output).  Resolve it LAZILY: prelude/load.scm loads
;; (emacs gobble) before (emacs tty-output), so an eager #:use-module
;; would invert that order (the same idiom as %kbd-buffer-store-event!
;; and read-key-sequence.scm).
(define %tty-handle-ebadf
  (delay (module-ref (resolve-module '(emacs tty-output))
                     'tty-handle-ebadf)))

;; Force the 1 memoized promise of this module OUTSIDE the input path
;; (review cr.org G4).  (emacs tty-output) calls this 1 time when it
;; loads, at which point =tty-handle-ebadf= exists: the prelude loads
;; (emacs gobble) FIRST, so a load-time force here would run too early,
;; and the warm step must come from the defining module.  Answer the
;; forced EBADF (a positive fixnum).  It is called for its effect only, so
;; a failure of the caller's resolve leaves the promise lazy and the
;; read entry still works.
(define (prime-input-handle!)
  (force %tty-handle-ebadf))

;; --- M63 imp-2: the input-handle helpers -----------------------------

;; Resolve DEVICE to the borrowed INPUT identity.  Answer the RAW leaf
;; value: a positive identity, 0 ("no identity yet"), or a negative
;; fixnum holding a bootstrap errno (-EBADF no tty, -ENOSPC full table).
;; Do NOT collapse a failure to #f: 0 and a negative fixnum are 2
;; DIFFERENT answers and the caller keeps them apart.  This is the ONE
;; resolve site and the ONE bootstrap call of the read path; the call is
;; idempotent, so a 2nd resolve of the same tty answers the same number
;; and moves no state.
;;
;; WARNING: the leaf is the REGISTER leaf, not a plain lookup.  A tty that
;; the table already holds answers the same identity, but a tty that it
;; does not hold gets a NEW slot, and a full table answers -ENOSPC.  So a
;; READ can now fill the shared 16-slot table, and an output-only workload
;; can stall input.  That is limit row 8 and it stays OPEN in imp-2: the
;; read path has no plain-lookup leaf yet.
(define (input-handle-id device)
  ((force %--tty-handle) device))

;; Read the state word: +input-borrowed+, +input-open+ or +input-closed+.
;; An identity the C table does not hold answers +input-closed+, as a
;; plain number and not an error.
(define (input-handle-state id)
  ((force %--m63-input-state) id))

;; Move the handle to open.  Answer 0, or the negated EBADF when the
;; identity names no slot or the slot is CLOSED.  It is idempotent on an
;; open slot and the read body runs it on a POSITIVE count only.  CLOSED
;; is FINAL, because a closed slot means "the handle names no live
;; stream", so this call can not revive a handle that input-handle-close!
;; or delete_tty closed.
(define (input-handle-open! id)
  ((force %--m63-input-open!) id))

;; Move the handle to closed.  Answer 0, or the negated EBADF.  It closes
;; the state word only; the descriptor, the FILE * and the borrowed
;; identity stay as they are, so the teardown is still imp-4.  CLOSED is
;; FINAL: a later input-handle-open! answers the negated EBADF.
(define (input-handle-close! id)
  ((force %--m63-input-close!) id))

;; event_kind NO_EVENT is the first enum member (termhooks.h), value 0.
(define +no-event-kind+ 0)

;; KBD_BUFFER_SIZE is 4096 (src/keyboard.h) and the tty read caps a single
;; emacs_read batch at KBD_BUFFER_SIZE - 1 = 4095 bytes ("avoids reading
;; more than the kbd_buffer can really hold").  Hardcoded with a comment,
;; mirroring kbd-buffer.scm's own private KBD-BUFFER-SIZE — there is no
;; shared export for these, and they silently diverge only if C changes
;; them.
(define +kbd-buffer-size+ 4096)
(define +cbuf-cap+       4095)   ; KBD_BUFFER_SIZE - 1

;; kbd-buffer-store-event! lives in (emacs kbd-buffer), which is not
;; imported eagerly (see module comment).  Resolve it lazily at call
;; time via a delayed module-ref, mirroring read-key-sequence.scm.
(define %kbd-buffer-store-event!
  (delay (module-ref (resolve-module '(emacs kbd-buffer))
                     'kbd-buffer-store-event!)))

(define (store-user-signal-events!)
  "Port of store_user_signal_events (src/keyboard.c pre-M25 body):
for every registered signal with pending events, store one
USER_SIGNAL_EVENT per pending count and reset it to zero.  Returns nil."
  (for-each
   (lambda (sig)
     (let loop ((n ((force %--user-signal-pending) sig)))
       (when (> n 0)
         ((force %kbd-buffer-store-event!)
          ((force %--ie-user-signal-event) sig) #f)
         (loop ((force %--user-signal-pending-decrement!) sig)))))
   ((force %--user-signal-list)))
  #nil)

(define (handle-async-input!)
  "Port of handle_async_input (pre-imp-2 C body): call gobble-input
until it reports no more input (0) or a blocked read (negative).  The
dropped-platform urgent-query check was deleted, not ported.  Returns
nil."
  (let loop ()
    (when (> ((force %--gobble-input)) 0)
      (loop)))
  #nil)

(define (process-pending-signals!)
  "Port of process_pending_signals (pre-imp-2 C body): clear the
pending-signals flag, drain async input, then run any due atimers.
Order matches the C original exactly.  Returns nil."
  ((force %--pending-signals-clear!))
  (handle-async-input!)
  ((force %--do-pending-atimers!))
  #nil)

(define (gobble-input!)
  "Port of gobble_input (src/keyboard.c, pre-imp-3 C body): store any
pending user-signal events, then walk the terminal list newest-first
and drain each terminal's read_socket_hook until it reports <= 0.
Returns the total number of input chars read, or -1 when a terminal
errored and nothing was read overall.

Walk order: the C original walks physical terminal_list, which is
newest-first (new terminals are prepended).  The elisp terminal-list
primes while walking terminal_list head to tail without a final
nreverse, so it returns oldest-first; reverse it to match.  The drain
call, the nr == -2 terminal-death arm, and pending_signals all live
behind C shims (a raw hook pointer, terminate_due_to_signal, and a
signal-handler-written cell respectively)."
  (store-user-signal-events!)
  (let loop ((terms (reverse ((force %terminal-list))))
             (total 0)
             (err #f))
    (if (null? terms)
        (if (and err (= total 0)) -1 total)
        (let* ((term (car terms))
               (rest (cdr terms)))
          (if (not (eq? ((force %--terminal-read-socket-hook-p) term) #nil))
              ;; This terminal has a read_socket_hook.
              (if (eq? ((force %--input-blocked-p)) #nil)
                  ;; Input not blocked: drain this terminal, then the
                  ;; C shim has already handled a nr == -2 death.  Read
                  ;; the ie-smob's kind now (before the next drain call
                  ;; reuses the static storage) and store the quit event
                  ;; if the drain set one.
                  (let ((res ((force %--terminal-read-socket-hook!) term)))
                    (let ((nread (car res))
                          (nr (cadr res))
                          (ie (caddr res)))
                      ;; Pointer visible only on a clean end (nr 0); a
                      ;; nr -1 error or a -2 death (already deleted the
                      ;; terminal) do not touch pointers.
                      (when (= nr 0)
                        (for-each
                         (lambda (frame)
                           (when (eq? ((force %frame-terminal) frame) term)
                             ((force %--frame-make-pointer-visible!) frame)))
                         ((force %frame-list))))
                      (when (not (= ((force %--ie-kind) ie)
                                    +no-event-kind+))
                        ((force %kbd-buffer-store-event!) ie #f))
                      (loop rest (+ total nread) (or err (= nr -1)))))
                  ;; Input blocked: remember it and stop the whole walk.
                  (begin
                    ((force %--pending-signals-set!))
                    (if (and err (= total 0)) -1 total)))
              ;; Hookless terminal: skip without touching it.
              (loop rest total err))))))

(define (%tty-read-bytes! terminal id)
  "Internal port of the post-guard body of tty_read_avail_input
(src/keyboard.c, pre-imp-4 C body): size a nonblocking read of
TERMINAL's tty, emacs_read the available bytes, then decode each raw byte's
meta bit into an ASCII_KEYSTROKE_EVENT and store it via
kbd-buffer-store-event!, stopping the decode early once a byte equal to
the (meta-stripped) quit char is seen.

M63 imp-2: this is the BODY only.  The exported tty-read-avail-input!
runs step 1 (resolve ID) and step 2 (read the state); step 4 (OPEN) runs
HERE, after the count test, so a read that delivers 0 bytes moves no
state.  The body then decodes the bytes of the borrowed IDENTITY.

The raw guards — dead terminal, terminal type, term_initted, suspended
input — already ran in the C entry point tty_read_avail_input before it
dispatched here, and the GPM drain also stayed in C.  This body runs the
kbd_on_hold_p / buffer_free guard, FIONREAD sizing, the read, the decode
and the store.  Returns the full number of bytes read from the tty
(nread), even when the quit-char batch-break stopped the decode early —
the return is the read count, not the number of bytes stored.

Per-byte fidelity (must match the C original's order of operations): the
meta modifier is computed from the ORIGINAL byte's high bit (when
meta_key == 1), the byte is then stripped to 7 bits (only when
meta_key < 2), and the STRIPPED code is compared against quit char.
Getting the strip/compute order backwards silently zeroes the meta
modifier.  See brief.org M25 imp-4."
  (let* ((nr-stored ((force %--kbd-buffer-nr-stored)))
         (buffer-free (- +kbd-buffer-size+ nr-stored 1)))
    (if (or (not (eq? ((force %--kbd-on-hold-p)) #nil))
            (<= buffer-free 0))
        0
        (let ((n-avail ((force %--tty-bytes-readable) terminal)))
          (if (<= n-avail 0)
              n-avail            ; 0 (nothing) or -2 (FIONREAD error)
              ;; Don't read more than the kbd_buffer can hold, nor more
              ;; than the remaining free slots.
              (let* ((count (min n-avail +cbuf-cap+ buffer-free))
                     (res ((force %--tty-read-nonblocking) terminal count)))
                (if (not (pair? res))
                    res          ; EIO close-terminal arm: bare -2
                    (let ((nread (car res)))
                      (if (<= nread 0)
                          nread  ; 0 or a raw -1 read error
                          (let ((bv (cdr res))
                                (meta-key ((force %--tty-meta-key) terminal))
                                (quit ((force %--quit-char)))
                                (frame ((force %--tty-top-frame) terminal)))
                            ;; M63 imp-2: step 3, OPEN on a POSITIVE count
                            ;; only.  Idempotent, so a 2nd read of this
                            ;; handle answers 0 and changes no state.  The
                            ;; state stays BORROWED until a byte arrives.
                            ;; The answer is CHECKED: step 2 of the entry
                            ;; gates a closed handle, but the slot can
                            ;; close between the 2 steps, and a negative
                            ;; answer must store no byte.  So both sites
                            ;; enforce "CLOSED is FINAL".
                            (let ((open (input-handle-open! id)))
                              (if (negative? open)
                                  ;; The slot is gone or CLOSED: answer
                                  ;; the negated EBADF of the leaf and
                                  ;; drop the bytes of this read.
                                  open
                                  (begin
                                    (let decode ((i 0))
                                      (when (< i nread)
                                        (let* ((b (bytevector-u8-ref bv i))
                                               ;; Compute modifiers from the
                                               ;; original byte, strip after.
                                               (mods (if (and (= meta-key 1)
                                                              (not (zero? (logand b #x80))))
                                                         meta-modifier
                                                         0))
                                               (code (if (< meta-key 2)
                                                         (logand b #x7f)
                                                         b)))
                                          ((force %kbd-buffer-store-event!)
                                           ((force %--ie-ascii-keystroke-event)
                                            code mods frame)
                                           #f)
                                          ;; Don't look at input that follows a
                                          ;; C-g too closely (reduces lossage due
                                          ;; to autorepeat on C-g).  The matching
                                          ;; byte is already stored above; bytes
                                          ;; after it in this batch are dropped.
                                          (unless (= code quit)
                                            (decode (+ i 1))))))
                                    ;; Return the read count, not the stored
                                    ;; count — the quit break may have stopped
                                    ;; the decode.
                                    nread)))))))))))))

;; --- M63 imp-2: the exported read entry ------------------------------

;; The C dispatcher calls this with the terminal object.  The 3 steps at
;; the head are the whole contract of this act:
;;
;;   1. RESOLVE.  ONE resolve site: the body calls (input-handle-id
;;      terminal) and never %--tty-handle itself.  The identity is
;;      BORROWED from the table that init_tty already fills, so
;;      --tty-handle answers the SAME number for a known tty.  The
;;      helper answers the RAW value, and the 3 answers stay apart: a
;;      positive fixnum is an identity; 0 is "no identity yet"; a
;;      negative fixnum is a BOOTSTRAP errno (-ENOSPC full table,
;;      -EBADF no tty).  The last 2 both answer 0 ("no input now") here
;;      and neither signals, because the input path has no arm that can
;;      report an errno.  A full table therefore stalls that terminal;
;;      the stall is limit row 8 of milestone.org section 5 and it stays
;;      OPEN.  LIMIT: this arm merges 2 different bootstrap answers (0 and
;;      a negative errno) into the SAME answer 0, so the "3 answers stay
;;      apart" rule holds in the helper only.  Add no reader that needs to
;;      tell them apart without a new leaf.
;;      A DEAD terminal never reaches here: the C entry point answers 0
;;      when !terminal->name (src/keyboard.c), and the terminal-list walk
;;      skips a dead tty.  MEASURED: if it did reach here, --tty-handle
;;      would NOT register a fresh identity and would NOT answer -EBADF:
;;      decode_tty_terminal -> decode_live_terminal SIGNALS
;;      wrong_type_argument (Qterminal_live_p) when t->name is NULL.  So
;;      a resolve after delete_tty can not bypass the CLOSED gate.  That
;;      signal is the last line of defence; imp-4 must keep it.
;;   2. READ THE STATE.  +input-closed+ has 2 sources: delete_tty (the
;;      identity is gone) and (input-handle-close! id), which closes the
;;      state while the descriptor stays open.  Answer the negated EBADF
;;      from the ONE Scheme definition and store no byte; do NOT call the
;;      read leaf.
;;   3. OPEN.  Runs inside the body, on a POSITIVE count only, and the
;;      body CHECKS its answer: step 2 gates most closed handles, but the
;;      slot can close between step 2 and step 3, so a negative answer
;;      stores no byte either.  Both sites enforce "CLOSED is FINAL".
;;      A negative answer here comes AFTER the read leaf took the bytes
;;      from the descriptor, so that batch is DROPPED and the caller gets
;;      an errno in place of a count.  This arm is unreachable while 1
;;      read runs in 1 thread and nothing closes the slot between the 2
;;      steps; it is defensive.  The answer -EBADF stays, and is not 0,
;;      because a closed handle must not read as "no input now".  The
;;      dropped batch is a declared limit.
;;
;; The BYTE COUNT stays the return value of the body.  This module is
;; #:declarative? #t and holds no mutable STATE WORD, so the count can not
;; outlive the call and is not persisted.  It does hold ONE memoized
;; promise (%tty-handle-ebadf): after the first force the module holds
;; that cell, so do not read this rule as "the module is stateless".
(define (tty-read-avail-input! terminal)
  "Read the available bytes of TERMINAL through the opaque INPUT handle.
The C dispatcher already ran the raw guards.  Returns the plain read
count (0 or a positive fixnum), or a negative fixnum when the handle is
closed or the read itself fails.  The count is the return value only: no
copy of it is stored, so C holds none."
  (let ((id (input-handle-id terminal)))
    (cond
     ;; 1. RESOLVE, arm A: not a fixnum at all.  The leaf answers 1 fixnum
     ;; and SIGNALS a wrong-type error for a bad DEVICE.  It never answers
     ;; a non-fixnum, so this arm can not run today.  Keep it as a
     ;; defensive guard only, and do NOT read it as "a bad DEVICE answers
     ;; no input now": the leaf signals that case, and it stays a signal.
     ((not (integer? id)) 0)
     ;; 1. RESOLVE, arm B: no identity yet (0 or a negative bootstrap
     ;; error).  -ENOSPC (full table) and -EBADF (no tty) are real errors
     ;; of the BOOTSTRAP, not of the read.  Answer 0 and do not signal;
     ;; the terminal then stalls.
     ((<= id +no-identity+) 0)
     ;; 2. READ THE STATE: closed means delete_tty dropped the identity,
     ;; or a caller ran input-handle-close!.  CLOSED is FINAL, so no later
     ;; open! revives it.
     ((= (input-handle-state id) +input-closed+)
      (- (force %tty-handle-ebadf)))
     ;; 3. OPEN (inside the body), then the bytes.
     (else (%tty-read-bytes! terminal id)))))
