;;; kbd-buffer.scm --- M11 imp-2: Scheme wait-loop port (kbd_buffer_get_event)
;;;
;;; Ports the prelude + for(;;) wait loop + post-wait prologue of C
;;; kbd_buffer_get_event (src/keyboard.c:4965-5127) as the entry
;;; procedure `kbd-buffer-get-event'.  Pure transliteration — no
;;; algorithmic change; the C body stays callable until the imp-5
;;; cutover.  See docs/m11-plan.org §imp-2.
;;;
;;; Conventions (identical to M9/M10): defelisp delayed references for
;;; every C DEFUN ((force %--foo)); elisp variables via symbol-value /
;;; set-symbol-value! (C-backed at runtime); #nil is elisp nil.
;;; No module-level mutable state (Risk 3 — re-entrancy): every flag
;;; is a let-local of the single invocation; the only shared state is
;;; the C ring buffer itself.

(define-module (emacs kbd-buffer)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:use-module (emacs read-char)      ; rc-state-kbp / set-rc-state-kbp! etc.
  #:declarative? #t
  #:export (kbd-buffer-get-event
            noninteractive-fast-path?))

;;; --- Constants ------------------------------------------------------

;; KBD_BUFFER_SIZE is 4096 (src/keyboard.h:379); the unhold threshold
;; is KBD_BUFFER_SIZE / 4 = 1024.  Hardcoded with a comment — there is
;; no DEFUN for it, and this silently diverges if C changes it.
(define KBD-BUFFER-SIZE/4 1024)

;;; --- C DEFUN references ---------------------------------------------

(defelisp %--kbd-on-hold-p              --kbd-on-hold-p)
(defelisp %--kbd-buffer-nr-stored       --kbd-buffer-nr-stored)
(defelisp %--unhold-keyboard-input      --unhold-keyboard-input)
(defelisp %--kbd-noninteractive-getchar --kbd-noninteractive-getchar)
(defelisp %--rc-write-kbp               --rc-write-kbp)
(defelisp %--rc-record                  --rc-record)
(defelisp %--rc-end-time-expired-p      --rc-end-time-expired-p)
(defelisp %--rc-end-time-remaining      --rc-end-time-remaining)
(defelisp %--wait-reading-process-output --wait-reading-process-output)
(defelisp %--kbd-wait-do-display-p      --kbd-wait-do-display-p)
(defelisp %--detect-conversion-events   --detect-conversion-events)
(defelisp %--kbd-fetch-ptr-index        --kbd-fetch-ptr-index)
(defelisp %--kbd-store-ptr-index        --kbd-store-ptr-index)
(defelisp %--some-mouse-moved           --some-mouse-moved)
(defelisp %--quit-throw-to-read-char    --quit-throw-to-read-char)
(defelisp %--gobble-input               --gobble-input)
(defelisp %--x-detect-pending-selection-requests
          --x-detect-pending-selection-requests)
(defelisp %--x-handle-pending-selection-requests
          --x-handle-pending-selection-requests)
(defelisp %--interrupt-input-p          --interrupt-input-p)
(defelisp %--handle-pending-conversion-events
          --handle-pending-conversion-events)
(defelisp %--conversion-disabled-p      --conversion-disabled-p)
(defelisp %daemonp                      daemonp)
(defelisp %--daemon-not-yet-running-p   --daemon-not-yet-running-p)
(defelisp %current-kboard               current-kboard)

;;; --- Helpers ---------------------------------------------------------

(define (truthy? x)
  "Elisp truthiness: everything except #nil is true."
  (not (eq? x #nil)))

(define (noninteractive-fast-path?)
  "t when the C noninteractive/daemon fast path applies, i.e. the
exact C boolean `noninteractive || (IS_DAEMON && DAEMON_RUNNING)'
(keyboard.c:4991-4994).  Scheme gate for the
--kbd-noninteractive-getchar branch.  Note that a t here does NOT
guarantee the fast path returns: --kbd-noninteractive-getchar returns
nil (fall through to the wait loop) on builds compiled with DBus /
file-notify / threads, where C compiles the whole block out."
  (or (truthy? (symbol-value 'noninteractive))
      (and (truthy? ((force %daemonp)))
           (not (truthy? ((force %--daemon-not-yet-running-p)))))))

(define (entry-sync rec kbp end-time)
  "imp-2 entry sync: if a rec is current (REC non-nil) and its
kbp / end-time slots are #nil while the corresponding arg is a non-nil
foreign pointer, copy the arg into the slot (set-rc-state-kbp! /
set-rc-state-end-time!).  This makes the rec-based write-back DEFUNs
(--rc-write-kbp, --rc-end-time-expired-p, --rc-end-time-remaining)
work during imp-2, before imp-5 wires RC_SLOT_KBP.  Production
equivalence holds because the rec slots and the shim args carry the
same pointers."
  (when (not (eq? rec #nil))
    (when (and (eq? (rc-state-kbp rec) #nil)
               (not (eq? kbp #nil)))
      (set-rc-state-kbp! rec kbp))
    (when (and (eq? (rc-state-end-time rec) #nil)
               (not (eq? end-time #nil)))
      (set-rc-state-end-time! rec end-time))))

(define (prelude-unhold)
  "C 4982-4987: start reading input again once the queue has drained
below a quarter of KBD_BUFFER_SIZE.  No-op when input is not held
(--kbd-on-hold-p nil on builds without subprocesses)."
  (when (and (truthy? ((force %--kbd-on-hold-p)))
             (< ((force %--kbd-buffer-nr-stored)) KBD-BUFFER-SIZE/4))
    ((force %--unhold-keyboard-input))))

;;; --- imp-2 → imp-3/imp-4 seam ----------------------------------------

;;; The C post-wait hands off to the event-kind dispatch switch (imp-3)
;;; when the queue is non-empty, or mouse-motion synthesis (imp-4)
;;; otherwise.  imp-2 leaves both as clearly-throwing stubs; imp-3/4
;;; replace them in-module.  imp-2's tests never legitimately reach
;;; them (a stuffed queue needs imp-1.4 — pulled forward — and the
;;; dispatch itself needs imp-3), so the throws are honest and safe.

(define (dispatch-event!)
  "imp-3 seam: the switch (event->kind) dispatch of
kbd_buffer_get_event.  Not implemented in imp-2."
  (throw 'not-implemented "imp-3/imp-4"))

(define (mouse-motion-synthesize!)
  "imp-4 seam: the some_mouse_moved () fallback (make_lispy_movement).
Not implemented in imp-2."
  (throw 'not-implemented "imp-3/imp-4"))

;;; --- kbd-buffer-get-event --------------------------------------------

(define (kbd-buffer-get-event kbp used-mouse-menu end-time)
  "Port of C kbd_buffer_get_event (keyboard.c:4965-5127): entry sync,
hold/unhold prelude, noninteractive/daemon fast path, *kbp =
current_kboard, the for(;;) wait loop, and the post-wait prologue
(selection handling → Vunread drain → text-conversion preamble →
dispatch hand-off).  KBP and END-TIME are pointer-smobs (or #nil),
matching the planned imp-5 SCM_CALL_3 shim; USED-MOUSE-MENU is unused
by imp-2 (imp-3 writes it via --rc-mark-used-mouse-menu-true)."
  (let ((rec ((force %--rc-record))))
    (entry-sync rec kbp end-time)
    (prelude-unhold)
    (let ((had-sel #f)
          (had-conv #f))

      ;; C 5003: *kbp = current_kboard (no-op when no rec is on the
      ;; stack — --rc-write-kbp is a guarded no-op at rc depth 0).
      (define (write-kbp!)
        ((force %--rc-write-kbp) ((force %current-kboard))))

      ;; C 5011-5035 — top-of-loop checks.  Each break yields an exit
      ;; symbol; the quit branch never returns (longjmp to the
      ;; read-char wait point — nothing after it is relied upon).
      (define (first-check)
        (cond
         ((pair? (symbol-value 'unread-command-events)) 'vunread)
         ((truthy? ((force %--detect-conversion-events)))
          (set! had-conv #t)
          'conv)
         ((not (= ((force %--kbd-fetch-ptr-index))
                  ((force %--kbd-store-ptr-index))))
          'queue)
         ((truthy? ((force %--some-mouse-moved))) 'mouse)
         ((truthy? (symbol-value 'quit-flag))
          ((force %--quit-throw-to-read-char)))   ; never returns
         (else #f)))

      ;; C 5044-5053 — post-gobble re-checks (selection requests join).
      (define (second-check)
        (cond
         ((not (= ((force %--kbd-fetch-ptr-index))
                  ((force %--kbd-store-ptr-index))))
          'queue)
         ((truthy? ((force %--some-mouse-moved))) 'mouse)
         ((truthy? ((force %--x-detect-pending-selection-requests)))
          (set! had-sel #t)
          'sel)
         (else #f)))

      ;; C 5055-5085 — timed vs untimed wait.  The timed branch only
      ;; applies when a rec is current AND an end-time arg was passed;
      ;; outside a rec end-time is treated as unset (matching
      ;; --rc-end-time-expired-p's depth-0 nil behavior).  Returns #t
      ;; when the deadline expired (caller returns nil), #f to
      ;; re-iterate.
      (define (timed?)
        (and (not (eq? rec #nil))
             (not (eq? end-time #nil))))

      (define (deadline-wait!)
        (if (timed?)
            (if (truthy? ((force %--rc-end-time-expired-p)))
                #t                    ; C: return Qnil (finished waiting)
                (let ((remaining ((force %--rc-end-time-remaining))))
                  ;; TOCTOU guard: the deadline may have crossed between
                  ;; --rc-end-time-expired-p and --rc-end-time-remaining
                  ;; (both call current_timespec independently); a nil
                  ;; remaining means expired → return nil, no wait.
                  (if (eq? remaining #nil)
                      #t
                      (begin
                        ((force %--wait-reading-process-output)
                         (car remaining) (cdr remaining) -1 1)
                        #f))))
            (begin
              ((force %--wait-reading-process-output)
               0 0 -1 ((force %--kbd-wait-do-display-p)))
              #f)))

      ;; C 5087-5088 — CBREAK mode: gobble after the wait, but only if
      ;; the queue is still empty (the wait may have stuffed events).
      (define (cbreak-gobble!)
        (when (and (eq? ((force %--interrupt-input-p)) #nil)
                   (= ((force %--kbd-fetch-ptr-index))
                      ((force %--kbd-store-ptr-index))))
          ((force %--gobble-input))))

      ;; C 5091-5127 — post-wait prologue.  Order is exact: selection
      ;; handling, then the Vunread drain (outranks everything — a
      ;; 'conv exit with a non-empty Vunread returns the Vunread
      ;; event), then the text-conversion preamble (returns
      ;; Qtext_conversion or nil, bypassing dispatch), then the
      ;; dispatch hand-off decided by the re-checked queue state (as
      ;; C does, not by the exit symbol).
      (define (post-wait)
        (when had-sel
          ((force %--x-handle-pending-selection-requests)))
        (let ((v (symbol-value 'unread-command-events)))
          (if (pair? v)
              (let ((first (car v)))
                (set-symbol-value! 'unread-command-events (cdr v))
                (write-kbp!)
                first)
              (if had-conv
                  (begin
                    ((force %--handle-pending-conversion-events))
                    (if (or (truthy? ((force %--conversion-disabled-p)))
                            (eq? (symbol-value 'text-conversion-edits) #nil))
                        #nil
                        'text-conversion))
                  (if (not (= ((force %--kbd-fetch-ptr-index))
                              ((force %--kbd-store-ptr-index))))
                      (dispatch-event!)
                      (mouse-motion-synthesize!))))))

      (define (wait-loop)
        (let loop ()
          (let ((exit (first-check)))
            (if exit
                (post-wait)
                (begin
                  ;; C 5041 — gobble unconditionally (gobble_input is
                  ;; compiled unconditionally in this tree; the C
                  ;; USABLE_SIGIO/SIGPOLL #ifdef is a
                  ;; micro-optimization).
                  ((force %--gobble-input))
                  (let ((exit (second-check)))
                    (if exit
                        (post-wait)
                        (if (deadline-wait!)
                            #nil
                            (begin
                              (cbreak-gobble!)
                              (loop))))))))))

      ;; Fast path — C 4990-5001.  The #nil trap: on builds compiled
      ;; with DBus / file-notify / threads, --kbd-noninteractive-getchar
      ;; returns nil and the proc must NOT return that nil as an event —
      ;; it falls through to the wait loop (C compiles the whole block
      ;; out on such builds).
      (if (noninteractive-fast-path?)
          (let ((c ((force %--kbd-noninteractive-getchar))))
            (if (eq? c #nil)
                (begin (write-kbp!) (wait-loop))
                (begin (write-kbp!) c)))
          (begin (write-kbp!) (wait-loop))))))
