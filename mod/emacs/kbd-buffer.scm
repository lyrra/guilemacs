;;; kbd-buffer.scm --- M11 imp-2/imp-3: Scheme wait-loop + event-kind
;;;                    dispatch port (kbd_buffer_get_event)
;;;
;;; Ports the prelude + for(;;) wait loop + post-wait prologue (imp-2)
;;; and the switch (event->kind) dispatch block (imp-3) of C
;;; kbd_buffer_get_event (src/keyboard.c:5016-5547) as the entry
;;; procedure `kbd-buffer-get-event'.  Pure transliteration — no
;;; algorithmic change; the C body stays callable until the imp-5
;;; cutover.  See docs/m11-plan.org §imp-2/§imp-3.
;;;
;;; M12 imp-2: `kbd-buffer-get-event' now RETURNS
;;; (values event kboard used-mouse-menu) instead of writing *kbp /
;;; *used_mouse_menu through caller pointers.  The still-live M11 C
;;; shim (src/keyboard.c:5075-5100) is served by the temporary
;;; `kbd-buffer-get-event-write-back' adapter, which re-materialises the
;;; pointer write-backs from the returned values; imp-4 deletes the
;;; adapter together with the shim, its C caller, and the write-back
;;; DEFUNs.  See docs/m12-plan.org §imp-2.
;;;
;;; Conventions (identical to M9/M10): defelisp delayed references for
;;; every C DEFUN ((force %--foo)); elisp variables via symbol-value /
;;; set-symbol-value! (C-backed at runtime); #nil is elisp nil.
;;; No module-level mutable state (Risk 3 — re-entrancy): every flag
;;; is a let-local of the single invocation; the only shared state is
;;; the C ring buffer itself.
;;;
;;; ie-smob lifetime (Risk 2 — hard rule): make-lispy-event invalidates
;;; its ie-smob on return (the M9 shim NULLs SMOB_DATA), so any field
;;; needed AFTER that call (kind, frame-or-window, arg, used-mouse-menu
;;; classification) is extracted into a local BEFORE it.  Preamble
;;; reads (switch-frame detection, pinch coalescing, multibyte decode)
;;; may stay smob-sourced.

(define-module (emacs kbd-buffer)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:use-module (emacs read-char)      ; rc-state-end-time / set-rc-state-end-time!
  #:use-module (emacs lispy-event)    ; make-lispy-event (M9)
  #:declarative? #t
  #:export (kbd-buffer-get-event
            kbd-buffer-get-event-write-back
            noninteractive-fast-path?))

;;; --- Constants ------------------------------------------------------

;; KBD_BUFFER_SIZE is 4096 (src/keyboard.h:379); the unhold threshold
;; is KBD_BUFFER_SIZE / 4 = 1024.  Hardcoded with a comment — there is
;; no DEFUN for it, and this silently diverges if C changes it.
(define KBD-BUFFER-SIZE/4 1024)
;; The full size — ring-buffer index arithmetic wraps modulo this
;; (next_kbd_event, keyboard.c:409).
(define KBD-BUFFER-SIZE 4096)

;;; Virtual-core device names.  static Lisp_Object strings in C
;;; (keyboard.c:13690-13691) with no DEFUN/DEFVAR — hardcoded here with
;;; a comment; the values silently diverge only if C changes them.
(define VIRTUAL-CORE-KEYBOARD-NAME "Virtual core keyboard")
(define VIRTUAL-CORE-POINTER-NAME  "Virtual core pointer")

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
;; imp-3 — dispatch-switch infrastructure (see the DEFUN table in
;; brief.org).  Kinds / ie accessors / advance points.
(defelisp %--kbd-event-kind             --kbd-event-kind)
(defelisp %--kbd-event-ie               --kbd-event-ie)
(defelisp %--kbd-advance-fetch-ptr      --kbd-advance-fetch-ptr)
(defelisp %--update-input-pending       --update-input-pending)
(defelisp %--kbd-set-fetch-ptr-index    --kbd-set-fetch-ptr-index)
(defelisp %--kbd-handle-selection-event --kbd-handle-selection-event)
(defelisp %--activate-menubar-hook      --activate-menubar-hook)
(defelisp %--kbd-decode-multibyte-string
          --kbd-decode-multibyte-string)
(defelisp %--rc-mark-used-mouse-menu-true --rc-mark-used-mouse-menu-true)
(defelisp %--get-internal-last-event-frame
          --get-internal-last-event-frame)
(defelisp %--set-internal-last-event-frame
          --set-internal-last-event-frame)
(defelisp %--ie-kind                    --ie-kind)
(defelisp %--ie-code                    --ie-code)
(defelisp %--ie-modifiers               --ie-modifiers)
(defelisp %--ie-arg                     --ie-arg)
(defelisp %--ie-frame-or-window         --ie-frame-or-window)
(defelisp %--ie-kboard                  --ie-kboard)
(defelisp %--ie-device                  --ie-device)
(defelisp %--ie-clear                   --ie-clear)
(defelisp %--set-ie-arg                 --set-ie-arg)
(defelisp %--set-ie-code                --set-ie-code)
(defelisp %--ie-kind-from-name          --ie-kind-from-name)
(defelisp %--frame-focus-frame          --frame-focus-frame)
;; imp-4 — mouse-motion fallback shims (see brief.org §imp-4).
(defelisp %--mouse-position-hook        --mouse-position-hook)
(defelisp %--make-lispy-position        --make-lispy-position)
(defelisp %--make-scroll-bar-position   --make-scroll-bar-position)
(defelisp %--frame-last-mouse-device    --frame-last-mouse-device)
(defelisp %--kbd-abort                  --kbd-abort)
;; Elisp primitives (Scheme-backed or C DEFUNs) via %c.
(defelisp %setcar                       setcar)
(defelisp %aref                         aref)
(defelisp %length                       length)
(defelisp %apply                        apply)
(defelisp %stringp                      stringp)
(defelisp %windowp                      windowp)
(defelisp %window-frame                 window-frame)
(defelisp %frame-live-p                 frame-live-p)
(defelisp %selected-frame               selected-frame)
(defelisp %run-hook-with-args           run-hook-with-args)

;;; --- Helpers ---------------------------------------------------------

(define (truthy? x)
  "Elisp truthiness: everything except #nil is true."
  (not (eq? x #nil)))

(define (noninteractive-fast-path?)
  "t when the C noninteractive/daemon fast path applies, i.e. the
exact C boolean `noninteractive || (IS_DAEMON && DAEMON_RUNNING)'
(keyboard.c:5042-5045).  Scheme gate for the
--kbd-noninteractive-getchar branch.  Note that a t here does NOT
guarantee the fast path returns: --kbd-noninteractive-getchar returns
nil (fall through to the wait loop) on builds compiled with DBus /
file-notify / threads, where C compiles the whole block out."
  (or (truthy? (symbol-value 'noninteractive))
      (and (truthy? ((force %daemonp)))
           (not (truthy? ((force %--daemon-not-yet-running-p)))))))

(define (entry-sync-end-time rec end-time)
  "Direct-invocation entry sync (M12 imp-2: end-time half only; the
kbp half died with the pointer parameters): when a rec is current (REC
non-nil) and its end-time slot is #nil while END-TIME is a non-nil
foreign pointer, copy the arg into the slot (set-rc-state-end-time!).
This makes the rec-based end-time DEFUNs (--rc-end-time-expired-p,
--rc-end-time-remaining) work when the proc is invoked directly from
Scheme (the test harness), where the C shim does not pre-fill the slot.

The M11 C shim now pre-fills RC_SLOT_END_TIME on every entry, so on
the production path the 'only fill nil slots' condition is already
false and this is a no-op.  That condition is what makes it safe to
keep: the rec slot and the shim arg carry the same pointer, so filling
from the arg is idempotent."

  (when (not (eq? rec #nil))
    (when (and (eq? (rc-state-end-time rec) #nil)
               (not (eq? end-time #nil)))
      (set-rc-state-end-time! rec end-time))))

(define (prelude-unhold)
  "C 5032-5039: start reading input again once the queue has drained
below a quarter of KBD_BUFFER_SIZE.  No-op when input is not held
(--kbd-on-hold-p nil on builds without subprocesses)."
  (when (and (truthy? ((force %--kbd-on-hold-p)))
             (< ((force %--kbd-buffer-nr-stored)) KBD-BUFFER-SIZE/4))
    ((force %--unhold-keyboard-input))))

;;; --- imp-2 → imp-3/imp-4 seam ----------------------------------------

;;; The C post-wait hands off to the event-kind dispatch switch (imp-3,
;;; implemented below) when the queue is non-empty, or mouse-motion
;;; synthesis (imp-4, mouse-motion-synthesize!) otherwise — except on X
;;; builds, where a pending selection request with an empty queue returns
;;; nil (C 5564-5567) rather than synthesizing or aborting.

;;; --- Event-kind constants (imp-3) ------------------------------------

;;; Event-kind integers via --ie-kind-from-name — the same mechanism
;;; (emacs lispy-event) register-kind! uses.  Bound unconditionally:
;;; kinds not compiled into C resolve to -1 and their case arms are
;;; dead, matching the C #ifdef discipline (such kinds never reach the
;;; buffer).  All immutable — no module-level mutable state (Risk 3).
(define SELECTION-REQUEST-EVENT     ((force %--ie-kind-from-name) 'selection-request-event))
(define SELECTION-CLEAR-EVENT       ((force %--ie-kind-from-name) 'selection-clear-event))
(define MONITORS-CHANGED-EVENT      ((force %--ie-kind-from-name) 'monitors-changed))
(define MENU-BAR-ACTIVATE-EVENT     ((force %--ie-kind-from-name) 'menu-bar-activate-event))
(define NOTIFICATION-EVENT          ((force %--ie-kind-from-name) 'notification-event))
(define NS-TEXT-EVENT               ((force %--ie-kind-from-name) 'ns-text-event))
(define PREEDIT-TEXT-EVENT          ((force %--ie-kind-from-name) 'preedit-text))
(define END-SESSION-EVENT           ((force %--ie-kind-from-name) 'end-session))
(define LANGUAGE-CHANGE-EVENT       ((force %--ie-kind-from-name) 'language-change))
(define DELETE-WINDOW-EVENT         ((force %--ie-kind-from-name) 'delete-frame))
(define ICONIFY-EVENT               ((force %--ie-kind-from-name) 'iconify-frame))
(define DEICONIFY-EVENT             ((force %--ie-kind-from-name) 'make-frame-visible))
(define MOVE-FRAME-EVENT            ((force %--ie-kind-from-name) 'move-frame))
(define FILE-NOTIFY-EVENT           ((force %--ie-kind-from-name) 'file-notify))
(define DBUS-EVENT                  ((force %--ie-kind-from-name) 'dbus-event))
(define THREAD-EVENT                ((force %--ie-kind-from-name) 'thread-event))
(define XWIDGET-EVENT               ((force %--ie-kind-from-name) 'xwidget-event))
(define XWIDGET-DISPLAY-EVENT       ((force %--ie-kind-from-name) 'xwidget-display-event))
(define SAVE-SESSION-EVENT          ((force %--ie-kind-from-name) 'save-session))
(define NO-EVENT                    ((force %--ie-kind-from-name) 'no-event))
(define HELP-EVENT                  ((force %--ie-kind-from-name) 'help-echo))
(define FOCUS-IN-EVENT              ((force %--ie-kind-from-name) 'focus-in))
(define CONFIG-CHANGED-EVENT        ((force %--ie-kind-from-name) 'config-changed-event))
(define FOCUS-OUT-EVENT             ((force %--ie-kind-from-name) 'focus-out))
(define SELECT-WINDOW-EVENT         ((force %--ie-kind-from-name) 'select-window))
(define ASCII-KEYSTROKE-EVENT       ((force %--ie-kind-from-name) 'ascii-keystroke))
(define MULTIBYTE-CHAR-KEYSTROKE-EVENT
  ((force %--ie-kind-from-name) 'multibyte-char-keystroke))
(define NON-ASCII-KEYSTROKE-EVENT   ((force %--ie-kind-from-name) 'non-ascii-keystroke))
(define PINCH-EVENT                 ((force %--ie-kind-from-name) 'pinch))
(define MENU-BAR-EVENT              ((force %--ie-kind-from-name) 'menu-bar))
(define TAB-BAR-EVENT               ((force %--ie-kind-from-name) 'tab-bar))
(define TOOL-BAR-EVENT              ((force %--ie-kind-from-name) 'tool-bar))
(define NS-NONKEY-EVENT             ((force %--ie-kind-from-name) 'ns-nonkey))

;;; --- imp-3 helpers ----------------------------------------------------

(define (elisp-t? x)
  "t when X is elisp t (C EQ (x, Qt)).  The runtime bridges Qt to
Scheme #t; the defensive 't check mirrors buffer-locals.scm:358."
  (or (eq? x #t) (eq? x 't)))

(define (fmod x y)
  "C fmod (libm): X - Y*trunc (X/Y) — the remainder with the sign of X.
Guile/elisp `mod' differ on negative angles (euclidean), so compute
fmod directly.  Used for the pinch-angle wrap (C:5398)."
  (- x (* y (truncate (/ x y)))))

;;; --- dispatch-event! (imp-3) -----------------------------------------

(define (dispatch-event!)
  "Port of the C switch (event->kind) dispatch block of
kbd_buffer_get_event (src/keyboard.c:5195-5480).  Reads the event at
the current fetch index — peek, not dequeue: the C does not advance
uniformly (switch-frame and unfinished multibyte-incremental leave the
event in the queue; pinch jumps past a whole run), so the fetch ptr is
advanced explicitly at exactly the C advance points.  Returns
(values event kboard used-mouse-menu): the Lisp event, or 'wait to
re-enter the wait loop for swallowed kinds; KBOARD is the F1 kboard
(--ie-kboard ie, current-kboard fallback — the deleted C queue-event
prologue as a value, cr.org); USED-MOUSE-MENU is #t when a
menu-bar / tab-bar / tool-bar / NS-nonkey event was dispatched.  The
caller (kbd-buffer-get-event) guarantees a non-empty queue."
  (let* ((idx ((force %--kbd-fetch-ptr-index)))
         (kind ((force %--kbd-event-kind) idx))
         (ie ((force %--kbd-event-ie) idx))
         ;; The C *used_mouse_menu bool, accumulated locally: C sets it
         ;; inside the switch (keyboard.c:5450-5468 + the NS_TEXT arm);
         ;; with no pointer, the flag is returned as the third value.
         (umm #nil))

    ;; C: if (used_mouse_menu) *used_mouse_menu = true.
    (define (mark-used-mouse-menu!)
      (set! umm #t))

    ;; Pass-through kinds: obj = make_lispy_event, then advance.
    ;; make-lispy-event invalidates IE on return (Risk 2), which is
    ;; fine — the result is the event; only the advance follows.
    (define (pass-through!)
      (let ((ev (make-lispy-event ie)))
        ((force %--kbd-advance-fetch-ptr))
        ev))

    ;; C 5320-5324: resolve event->frame_or_window to a frame — CONSP →
    ;; car, WINDOWP → window-frame, else as-is.
    (define (frame-or-window->frame fo-w)
      (cond
       ((pair? fo-w) (car fo-w))
       (((force %windowp) fo-w) ((force %window-frame) fo-w))
       (else fo-w)))

    ;; C 5361-5364: PINCH_EVENT arg is (DX DY <ignored> ANGLE); the
    ;; start of a gesture (all three zero) is never coalesced.
    (define (pinch-start? a)
      (and (= (car a) 0.0)
           (= (car (cdr a)) 0.0)
           (= (car (cdr (cdr (cdr a)))) 0.0)))

    ;; C 5356-5404.  Returns the index of the last coalesced event
    ;; (= the C `event' pointer after the loop), or IDX unchanged when
    ;; no coalescing applies.  Writes the running totals into each
    ;; skipped event's arg and tracks Vlast_event_device.
    ;;
    ;; GC-safety of the in-place setcar writes (Risk 1): kbd_buffer is
    ;; a C global, so the conservative GC (Fgarbage_collect →
    ;; GC_gcollect, alloc.c) treats the whole ring as a root — the
    ;; conses in ie.arg stay reachable while the event is queued, and
    ;; setcar goes through XSETCAR exactly as the C does
    ;; (keyboard.c:5394-5398).
    (define (pinch-coalesce! idx frame-or-window modifiers arg store)
      (if (or (not (= kind PINCH-EVENT))
              (pinch-start? arg))
          idx
          (let ((cur idx)
                (maybe (modulo (+ idx 1) KBD-BUFFER-SIZE))
                (dx (car arg))
                (dy (car (cdr arg)))
                (angle (car (cdr (cdr (cdr arg))))))
            (let loop ()
              (when (and (not (= maybe store))
                         (= ((force %--kbd-event-kind) maybe) PINCH-EVENT))
                (let* ((mie ((force %--kbd-event-ie) maybe))
                       (ma ((force %--ie-arg) mie)))
                  (when (and (= ((force %--ie-modifiers) mie) modifiers)
                             (eq? ((force %--ie-frame-or-window) mie)
                                  frame-or-window)
                             (not (pinch-start? ma)))
                    (set! dx (+ dx (car ma)))
                    (set! dy (+ dy (car (cdr ma))))
                    (set! angle (+ angle (car (cdr (cdr (cdr ma))))))
                    ;; Accumulated totals → this event's arg; angle
                    ;; wrapped with fmod (C:5394-5398).
                    ((force %setcar) ma dx)
                    ((force %setcar) (cdr ma) dy)
                    ((force %setcar) (cdr (cdr (cdr ma)))
                     (fmod angle 360.0))
                    ;; C:5400 — if (!EQ (device, Qt))
                    ;; Vlast_event_device = device.
                    (let ((d ((force %--ie-device) mie)))
                      (when (not (elisp-t? d))
                        (set-symbol-value! 'last-event-device d)))
                    (set! cur maybe)
                    (set! maybe (modulo (+ maybe 1) KBD-BUFFER-SIZE))
                    (loop)))))
            cur)))

    ;; C 5407-5431.  Returns 'wait when the decoded string is empty
    ;; (event dropped — advance + loop back), else the arg to feed the
    ;; incremental step (the original arg, or a fresh (0 . DECODED)).
    (define (multibyte-decode! arg)
      (if (and (= kind MULTIBYTE-CHAR-KEYSTROKE-EVENT)
               ((force %stringp) arg))
          (let ((s ((force %--kbd-decode-multibyte-string) arg)))
            ;; Decoding failed → keep the original, where at least
            ;; ASCII text will work (C:5417-5418).
            (if (eq? s #nil)
                (set! s arg))
            (if (= ((force %length) s) 0)
                (begin
                  ;; C:5420-5425 — empty decoded string: advance,
                  ;; obj = nil → loop back to wait.
                  ((force %--kbd-advance-fetch-ptr))
                  'wait)
                (let ((a (cons 0 s)))
                  ;; car = index of the next character to send, cdr =
                  ;; the string itself (C:5430).
                  ((force %--set-ie-arg) ie a)
                  a)))
          arg))

    ;; The C 5312-5480 default arm — the "real event" path.
    (define (default-path!)
      (let* ((frame-or-window ((force %--ie-frame-or-window) ie))
             (device ((force %--ie-device) ie))
             (arg ((force %--ie-arg) ie))
             (modifiers ((force %--ie-modifiers) ie))
             ;; (a) switch-frame synthesis (C:5317-5333).
             (frame (frame-or-window->frame frame-or-window))
             ;; F6: --frame-focus-frame returns nil for non-frames
             ;; (benign deviation from C's unconditional XFRAME abort);
             ;; a non-frame frame_or_window therefore flows through as-is.
             (focus ((force %--frame-focus-frame) frame))
             (frame (if (eq? focus #nil) frame focus))
             (obj (if (and (not (eq? frame ((force %--get-internal-last-event-frame))))
                           (not (eq? frame ((force %selected-frame)))))
                      (list 'switch-frame frame)
                      #nil)))
        ;; Continuous-record-currency (Risk 5): write
        ;; internal_last_event_frame at the mutation site (C:5333),
        ;; never batched at procedure return.
        ((force %--set-internal-last-event-frame) frame)
        ;; (b) device tracking (C:5335-5342).
        (set-symbol-value! 'last-event-device
                           (if (elisp-t? device)
                               (if (memv kind (list ASCII-KEYSTROKE-EVENT
                                                    MULTIBYTE-CHAR-KEYSTROKE-EVENT
                                                    NON-ASCII-KEYSTROKE-EVENT))
                                   VIRTUAL-CORE-KEYBOARD-NAME
                                   VIRTUAL-CORE-POINTER-NAME)
                               device))
        (if (not (eq? obj #nil))
            ;; (c) a switch-frame was generated — leave the event in
            ;; the queue for next time, return the switch-frame now.
            obj
            (let ((idx (pinch-coalesce! idx frame-or-window modifiers arg
                                        ((force %--kbd-store-ptr-index)))))
              ;; Re-wrap at the current index: the C calls
              ;; make_lispy_event on the LAST coalesced event, whose
              ;; arg holds the accumulated totals (Risk 2 — the
              ;; original smob must not outlive the wrap).
              (set! ie ((force %--kbd-event-ie) idx))
              (set! arg ((force %--ie-arg) ie))
              (let ((arg (multibyte-decode! arg)))
                (if (eq? arg 'wait)
                    'wait
                    (begin
                      ;; (c3) multibyte incremental (C:5433-5446):
                      ;; install the next character, bump the index.
                      (when (and (= kind MULTIBYTE-CHAR-KEYSTROKE-EVENT)
                                 (pair? arg))
                        (let ((str (cdr arg))
                              (i (car arg)))
                          ((force %--set-ie-code) ie
                           ((force %aref) str i))
                          ((force %setcar) arg (+ i 1))))
                      ;; (d) build the event (C:5448).
                      (let ((ev (make-lispy-event ie)))
                        ;; (e) used_mouse_menu (C:5450-5468) — the
                        ;; guards use locals extracted BEFORE
                        ;; make-lispy-event (it invalidates IE — Risk
                        ;; 2).  The !EQ (frame_or_window, arg) guard is
                        ;; only on the menu-bar group (C:5456-5461);
                        ;; NS_NONKEY_EVENT has none.
                        (when (or (and (not (eq? frame-or-window arg))
                                       (memv kind (list MENU-BAR-EVENT
                                                        TAB-BAR-EVENT
                                                        TOOL-BAR-EVENT)))
                                  (= kind NS-NONKEY-EVENT))
                          (set! umm #t))
                        ;; (f) cleanup (C:5470-5478): clear + advance,
                        ;; unless a multibyte incremental still has
                        ;; characters left (leave it in the queue).
                        (if (or (not (= kind MULTIBYTE-CHAR-KEYSTROKE-EVENT))
                                (not (pair? arg))
                                (>= (car arg) ((force %length) (cdr arg))))
                            (begin
                              ;; Wipe out this event, to catch bugs
                              ;; (clear_event).  Re-wrap: the smob was
                              ;; invalidated by make-lispy-event above.
                              ((force %--ie-clear)
                               ((force %--kbd-event-ie) idx))
                              ;; Advance past the (possibly coalesced)
                              ;; event — C: kbd_fetch_ptr =
                              ;; next_kbd_event (event).  Peek-first
                              ;; means the ptr still sits at the
                              ;; ORIGINAL index, so position it
                              ;; explicitly; modulo wraps the ring.
                              ((force %--kbd-set-fetch-ptr-index)
                               (modulo (+ idx 1) KBD-BUFFER-SIZE)))
                            #nil)
                        ev))))))))

    ;; F1 (cr.org): the deleted C queue-event prologue
    ;;   *kbp = event_to_kboard (&event->ie);
    ;;   if (*kbp == 0) *kbp = current_kboard;
    ;; ran for EVERY queue event, before the switch.  --ie-kboard
    ;; returns nil exactly when event_to_kboard returned NULL, so the
    ;; nil arm reproduces the current_kboard fallback.  Reads the
    ;; ORIGINAL ie (default-path! re-wraps it for pinch coalescing);
    ;; the kboard is RETURNED as the second value instead of written
    ;; through *kbp — computed before the switch, so swallowed kinds
    ;; still surface it (C wrote *kbp even when it then looped back).
    (define (dispatch!)
      (cond
     ;; --- Swallowed kinds (C:5197-5269): run the side effect, loop
     ;; back to wait — they never produce a Lisp event.  The C
     ;; returns Qnil and read_char's retry re-enters; 'wait re-enters
     ;; our wait loop directly.
     ;; Resolved (imp-5, was FIX-imp5-guilemacs): the 'wait loop-back
     ;; is semantically faithful to the C for(;;) re-iteration, so it
     ;; cannot starve timers / quit-flag any worse than vanilla C.
     ;; first-check re-tests quit-flag and the queue on every re-entry,
     ;; and wait_reading_process_output (the timer pump) is reached
     ;; exactly when C reached it — whenever both checks report no
     ;; input.
     ;; NB: `cond' + memv/=/kind, not `case' — Guile's `case' quotes
     ;; its clause datums (ice-9/boot-9.scm:496), so `((,KIND) ...)'
     ;; keys would never match.
     ((memv kind (list SELECTION-REQUEST-EVENT SELECTION-CLEAR-EVENT))
      ;; --kbd-handle-selection-event advances fetch-ptr itself
      ;; (keyboard.c:1407) — no explicit advance here.
      ((force %--kbd-handle-selection-event))
      'wait)
     ((= kind MONITORS-CHANGED-EVENT)
      ((force %--kbd-advance-fetch-ptr))
      ((force %--update-input-pending))
      ((force %run-hook-with-args) 'display-monitors-changed-functions
       ((force %--ie-arg) ie))
      'wait)
     ((= kind MENU-BAR-ACTIVATE-EVENT)
      ;; C 5258-5269 uses a bare XFRAME (no cons/window coercion) —
      ;; pass frame_or_window straight through; frame-live-p and the
      ;; DEFUN no-op on non-frames.
      (let ((frame ((force %--ie-frame-or-window) ie)))
        ((force %--kbd-advance-fetch-ptr))
        ((force %--update-input-pending))
        (when ((force %frame-live-p) frame)
          ((force %--activate-menubar-hook) frame)))
      'wait)
     ((= kind NOTIFICATION-EVENT)
      (let ((arg ((force %--ie-arg) ie)))
        ((force %--kbd-advance-fetch-ptr))
        ((force %--update-input-pending))
        ((force %apply) (car arg) (cdr arg)))
      'wait)
     ;; --- NS_TEXT_EVENT: set used_mouse_menu first, then fall
     ;; through to the PREEDIT_TEXT_EVENT handling — no Scheme
     ;; FALLTHROUGH, so call the shared pass-through directly.
     ((= kind NS-TEXT-EVENT)
      (mark-used-mouse-menu!)
      (pass-through!))
     ;; --- The pass-through kinds (C:5276-5311): obj =
     ;; make_lispy_event, advance.
     ((memv kind (list PREEDIT-TEXT-EVENT END-SESSION-EVENT
                       LANGUAGE-CHANGE-EVENT DELETE-WINDOW-EVENT
                       ICONIFY-EVENT DEICONIFY-EVENT MOVE-FRAME-EVENT
                       FILE-NOTIFY-EVENT DBUS-EVENT THREAD-EVENT
                       XWIDGET-EVENT XWIDGET-DISPLAY-EVENT
                       SAVE-SESSION-EVENT NO-EVENT HELP-EVENT
                       FOCUS-IN-EVENT CONFIG-CHANGED-EVENT
                       FOCUS-OUT-EVENT SELECT-WINDOW-EVENT))
      (pass-through!))
     (else
      (default-path!))))

    ;; F1 as a value: the event's kboard, returned with the dispatch
    ;; result (computed above the switch — see the F1 comment on the
    ;; dispatch! define).
    (let ((kb (let ((e ((force %--ie-kboard) ie)))
                (if (eq? e #nil) ((force %current-kboard)) e))))
      (call-with-values (lambda () (dispatch!))
        (lambda (ev)
          (values ev kb umm))))))

(define (mouse-motion-synthesize!)
  "imp-4: port of the some_mouse_moved () fallback branch of C
kbd_buffer_get_event (src/keyboard.c:5514-5563).  Called when the event
queue is empty but a frame has pending mouse movement; synthesizes a
switch-frame or mouse-movement event without touching the ring buffer.
Returns the event list; aborts (--kbd-abort, the C shared else's
emacs_abort) when no frame has pending movement.  That nil-frame path is
the C 5568-5571 emacs_abort invariant: post-wait (C 5515 / 5564-5571)
only routes to #nil when some_mouse_moved is nil AND a selection request
is pending, so a nil movement-frame here means neither condition held —
the impossible state C dumps core on.
Does NOT advance the fetch pointer or update
input_pending (the shared C epilogue, imp-2/imp-5 tail)."
  (let ((movement-frame ((force %--some-mouse-moved))))
    ;; C 5515 / 5568-5571: post-wait calls us when the queue is empty
    ;; and (some_mouse_moved OR not had-sel); a nil movement-frame here
    ;; means both are false, the impossible invariant C dumps core on
    ;; via the shared else.
    (when (eq? movement-frame #nil)
      ((force %--kbd-abort)))
    (let* ((hook ((force %--mouse-position-hook) movement-frame))
           ;; C 5531-5533: the hook takes &f and may rewrite it (pointer
           ;; under another frame, or NULL outside all frames during a
           ;; drag).  Returns (F BAR-WINDOW PART X Y T), or nil
           ;; (non-frame / termcap build with no hook).  Normalize nil
           ;; to a 6-#nil list so the field bindings below are uniform.
           (hook* (if (eq? hook #nil)
                      (list #nil #nil #nil #nil #nil #nil)
                      hook))
           (f (car hook*))
           (bar-window (cadr hook*))
           (part (caddr hook*))
           (x (cadddr hook*))
           (y (car (cddddr hook*)))
           (t (cadr (cddddr hook*)))
           (obj #nil))
      ;; C 5537-5552: switch-frame synthesis, guarded by x && f (C:5540).
      ;; NOTE x and f do NOT always coincide: XTmouse_position can leave
      ;; f == NULL with x/y still set (pointer outside all frames during a
      ;; drag, xterm.c:15265), so the f guard here is required, not a
      ;; redundant re-check of x.
      (when (and (truthy? x) (truthy? f))
        (let* ((focus ((force %--frame-focus-frame) f))
               (focus (if (eq? focus #nil) f focus)))
          (when (and (not (eq? focus
                               ((force %--get-internal-last-event-frame))))
                     (not (eq? focus ((force %selected-frame)))))
            (set! obj (list 'switch-frame focus)))
          ;; Continuous-record-currency (Risk 5): writeback at the
          ;; mutation site (C:5551), same as default-path!.
          ((force %--set-internal-last-event-frame) focus)))
      ;; C 5554-5557: movement synthesis — scroll-bar (bar-window
      ;; non-nil) vs ordinary.  make_lispy_movement /
      ;; make_lispy_switch_frame are static C, so inlined in Scheme
      ;; (imp-0 Design change #1).
      (when (and (truthy? x) (eq? obj #nil))
        (set! obj
              (if (truthy? bar-window)
                  (list 'scroll-bar-movement
                        ((force %--make-scroll-bar-position)
                         bar-window x y t part 'vertical-scroll-bar))
                  ;; C 5556-5557: the ordinary arm passes the UPDATED f,
                  ;; which may be nil when x is set but the pointer is
                  ;; outside every frame.  --make-lispy-position is
                  ;; nil-tolerant (mirrors C make_lispy_position's
                  ;; `if (f) ... else Qnil').
                  (list 'mouse-movement
                        ((force %--make-lispy-position) f x y t)))))
      ;; C 5559-5562: device tracking — the ORIGINAL movement_frame's
      ;; last_mouse_device (not the possibly-updated f), else the
      ;; virtual-core pointer name.
      (when (not (eq? obj #nil))
        (let ((d ((force %--frame-last-mouse-device) movement-frame)))
          (set-symbol-value! 'last-event-device
                             (if ((force %stringp) d)
                                 d
                                 VIRTUAL-CORE-POINTER-NAME))))
      obj)))

;;; --- kbd-buffer-get-event --------------------------------------------

(define (kbd-buffer-get-event end-time)
  "Port of C kbd_buffer_get_event (keyboard.c:5016-5182): entry sync,
hold/unhold prelude, noninteractive/daemon fast path, *kbp =
current_kboard, the for(;;) wait loop, and the post-wait prologue
(selection handling → Vunread drain → text-conversion preamble →
dispatch hand-off).  Returns (values event kboard used-mouse-menu):
KBOARD is the kboard the event belongs to (entry = current-kboard,
F1 = event-to-kboard on the dispatched event, F2 = current-kboard);
USED-MOUSE-MENU is #t when a menu-bar / tab-bar / tool-bar / NS-nonkey
event was dispatched.  END-TIME is a pointer-smob (or #nil); its
rec-slot sync (entry-sync-end-time) and the deadline-wait! timed branch
are unchanged from M11.  The still-live C shim calls this through the
temporary kbd-buffer-get-event-write-back adapter (M12 imp-2)."
  (let ((rec ((force %--rc-record))))
    (entry-sync-end-time rec end-time)
    (prelude-unhold)
    (let ((had-sel #f)
          (had-conv #f)
          ;; C 5054: *kbp = current_kboard — the initial KBOARD return
          ;; value; F1 (dispatch-event!) / F2 (mouse-motion) overwrite
          ;; it (see dispatch-event! / post-wait).
          (kboard ((force %current-kboard)))
          ;; The C *used_mouse_menu bool, accumulated per invocation.
          ;; C sets it only on the non-swallowed menu-bar / tab-bar /
          ;; tool-bar / NS paths, which always produce the returned
          ;; event; swallowed kinds never set it, so the local simply
          ;; mirrors the dispatched event's third value.
          (used-mouse-menu #nil))

      ;; C 5062-5086 — top-of-loop checks.  Each break yields an exit
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

      ;; C 5095-5104 — post-gobble re-checks (selection requests join).
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

      ;; C 5106-5136 — timed vs untimed wait.  The timed branch only
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

      ;; C 5138-5139 — CBREAK mode: gobble after the wait, but only if
      ;; the queue is still empty (the wait may have stuffed events).
      (define (cbreak-gobble!)
        (when (and (eq? ((force %--interrupt-input-p)) #nil)
                   (= ((force %--kbd-fetch-ptr-index))
                      ((force %--kbd-store-ptr-index))))
          ((force %--gobble-input))))

      ;; C 5142-5182 — post-wait prologue.  Order is exact: selection
      ;; handling, then the Vunread drain (outranks everything — a
      ;; 'conv exit with a non-empty Vunread returns the Vunread
      ;; event), then the text-conversion preamble (returns
      ;; Qtext_conversion or nil, bypassing dispatch), then the
      ;; dispatch hand-off decided by the re-checked queue state (as
      ;; C does, not by the exit symbol).
      ;; C 5534-5537 shared tail: recompute input_pending and sync
      ;; Vlast_event_frame to internal_last_event_frame, then return
      ;; OBJ.  The Vunread drain (C 5155-5160) and the timed-wait
      ;; deadline return (C 5106-5110) are the two early returns that
      ;; skip this tail in C.
      (define (epilogue! obj)
        ((force %--update-input-pending))
        (set-symbol-value! 'last-event-frame
                           ((force %--get-internal-last-event-frame)))
        obj)

      (define (post-wait)
        (when had-sel
          ((force %--x-handle-pending-selection-requests)))
        (let ((v (symbol-value 'unread-command-events)))
          (if (pair? v)
              (let ((first (car v)))
                (set-symbol-value! 'unread-command-events (cdr v))
                ;; C 5155-5160: early return, no tail — the entry
                ;; *kbp = current_kboard (C 5054) still applies to this
                ;; exit, so re-derive KBOARD from current-kboard.
                (set! kboard ((force %current-kboard)))
                (values first kboard used-mouse-menu))
              (values
               (epilogue!
                (if had-conv
                    (begin
                      ((force %--handle-pending-conversion-events))
                      (if (or (truthy? ((force %--conversion-disabled-p)))
                              (eq? (symbol-value 'text-conversion-edits) #nil))
                          #nil
                          'text-conversion))
                    (if (not (= ((force %--kbd-fetch-ptr-index))
                                ((force %--kbd-store-ptr-index))))
                        (call-with-values (lambda () (dispatch-event!))
                          (lambda (ev kb umm)
                            ;; F1: adopt the dispatched event's kboard;
                            ;; accumulate the used-mouse-menu flag (the
                            ;; C bool* persists across loop-backs).
                            (set! kboard kb)
                            (when (truthy? umm)
                              (set! used-mouse-menu #t))
                            ev))
                        ;; C 5515 / 5564-5571: the mouse-motion branch
                        ;; outranks the X pending-selection branch.  Only
                        ;; when some_mouse_moved is nil AND a selection
                        ;; request is pending (had-sel) does C return Qnil
                        ;; (read_char retries); with neither, the shared
                        ;; else aborts.  mouse-motion-synthesize! itself
                        ;; re-checks some_mouse_moved and aborts when no
                        ;; frame has pending movement (C 5568-5571).
                        (if (or (truthy? ((force %--some-mouse-moved)))
                                (not had-sel))
                            ;; F2 (cr.org): C 5524 sets *kbp = current_kboard
                            ;; inside the mouse-motion branch before the hook
                            ;; call.  The internal wait loop re-enters without
                            ;; re-running the entry binding, so a swallowed
                            ;; event's F1 kboard (event_to_kboard) would
                            ;; otherwise leak into the synthesized event's
                            ;; return value.
                            (begin
                              (set! kboard ((force %current-kboard)))
                              (mouse-motion-synthesize!))
                            #nil))))
               kboard used-mouse-menu))))

      (define (wait-loop)
        (let loop ()
          (let ((exit (first-check)))
            (if exit
                (let ((r (post-wait)))
                  ;; imp-3: dispatch-event! returns 'wait for swallowed
                  ;; events — re-enter the wait loop instead of
                  ;; returning it as an event (C returns nil and
                  ;; read_char's retry re-enters; see the comment on
                  ;; dispatch!).  post-wait adopted KBOARD /
                  ;; USED-MOUSE-MENU into the locals on its way out.
                  (if (eq? r 'wait)
                      (loop)
                      (values r kboard used-mouse-menu)))
                (begin
                  ;; C 5092 — gobble unconditionally (gobble_input is
                  ;; compiled unconditionally in this tree; the C
                  ;; USABLE_SIGIO/SIGPOLL #ifdef is a
                  ;; micro-optimization).
                  ((force %--gobble-input))
                  (let ((exit (second-check)))
                    (if exit
                        (let ((r (post-wait)))
                          (if (eq? r 'wait)
                              (loop)
                              (values r kboard used-mouse-menu)))
                        (if (deadline-wait!)
                            ;; C 5106-5110: timed-wait expiry returns
                            ;; Qnil (the second early return that skips
                            ;; the shared tail).
                            (values #nil kboard used-mouse-menu)
                            (begin
                              (cbreak-gobble!)
                              (loop))))))))))

      ;; Fast path — C 5041-5052.  The #nil trap: on builds compiled
      ;; with DBus / file-notify / threads, --kbd-noninteractive-getchar
      ;; returns nil and the proc must NOT return that nil as an event —
      ;; it falls through to the wait loop (C compiles the whole block
      ;; out on such builds).  The entry *kbp = current_kboard applies
      ;; to the fast-path exits (C 5054).
      (if (noninteractive-fast-path?)
          (let ((c ((force %--kbd-noninteractive-getchar))))
            (if (eq? c #nil)
                (begin (set! kboard ((force %current-kboard)))
                       (wait-loop))
                (begin (set! kboard ((force %current-kboard)))
                       (values c kboard used-mouse-menu))))
          (begin (set! kboard ((force %current-kboard)))
                 (wait-loop))))))

;;; --- Temporary values→write-back adapter (M12 imp-2) -----------------

;;; The M11 C shim kbd_buffer_get_event (src/keyboard.c:5075-5100)
;;; keeps its 3-arg, single-return contract until imp-4: it calls this
;;; adapter, which calls the values-returning kbd-buffer-get-event,
;;; writes the returned kboard / used-mouse-menu back through the
;;; rc-record slots the shim pre-fills (RC_SLOT_KBP /
;;; RC_SLOT_USED_MOUSE_MENU / RC_SLOT_END_TIME, keyboard.c:5089-5095),
;;; and returns the event.  KBP / USED-MOUSE-MENU pointer args are
;;; unused — the write-back DEFUNs read the rec slots, not the args.
;;; The shim only runs inside read_char (rc_state_depth > 0), so
;;; --rc-record is non-nil whenever the used-mouse-menu write fires.
;;; imp-4 deletes this adapter together with the shim, its C caller,
;;; and the write-back DEFUNs.
(define (kbd-buffer-get-event-write-back kbp used-mouse-menu end-time)
  (call-with-values (lambda () (kbd-buffer-get-event end-time))
    (lambda (event kboard umm)
      (when (not (eq? kboard #nil))
        ((force %--rc-write-kbp) kboard))
      (when (truthy? umm)
        ;; No rec guard: the shim only calls this adapter inside
        ;; read_char (rc_state_depth > 0), so --rc-record is non-nil.
        ((force %--rc-mark-used-mouse-menu-true) ((force %--rc-record))))
      event)))
