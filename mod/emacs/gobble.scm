;;; gobble.scm --- M25 imp-1 + imp-2 + imp-3: user-signal drain,
;;;                  async input, gobble_input terminal walk
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
  #:declarative? #t
  #:export (store-user-signal-events!
            handle-async-input!
            process-pending-signals!
            gobble-input!))

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

;; event_kind NO_EVENT is the first enum member (termhooks.h), value 0.
(define +no-event-kind+ 0)

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
dropped-platform HAVE_ANDROID urgent-query check was deleted, not
ported.  Returns nil."
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
