;;; keyboard-init.scm --- M27 imp-3: init_keyboard file-static resets
;;;   ((emacs keyboard-init))
;;;
;;; Moves the 19 file-static resets of init_keyboard out of
;;; src/keyboard.c and into Scheme, as init-keyboard!, mirroring the
;;; imp-2 kboard-lifecycle.scm convention.  src/keyboard.c keeps only
;;; the current-kboard re-init (current_kboard / wipe_kboard /
;;; init_kboard), the sigaction installs, and the signal / poll arms.
;;; See brief.org M27 imp-3.
;;;
;;; init-keyboard! writes every reset cell in C order:
;;;   1.  the 13 C cells through their existing / new DEFUN shims
;;;       (defelisp delayed references);
;;;   2.  the 6 elisp variables via (set-symbol-value! 'NAME #nil), a
;;;       Guile binding from (emacs-elisp runtime) — NOT %c, same
;;;       convention as interrupt.scm.
;;;
;;; The C dispatcher is invoked from init_keyboard (src/emacs.c:2234),
;;; which runs after load_guile_prelude (prelude/load.scm loads this
;;; module) and syms_of_keyboard (which registers the DEFUNs), so module
;;; and DEFUN registration are both complete before the first dispatch.
;;; No early-init hazard.
;;;
;;; virtual_core_pointer_name / virtual_core_keyboard_name were C
;;; static dead-writes, reclaimed at imp-5.  They are never read in C;
;;; Scheme uses its own string constants (emacs kbd-buffer).

(define-module (emacs keyboard-init)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)  ; set-symbol-value!
  #:declarative? #t
  #:export (init-keyboard!))

;; The 13 C shims — referenced by name through defelisp delays so they
;; resolve lazily after syms_of_keyboard registers the DEFUNs.
(defelisp %--command-loop-level-set!      --command-loop-level-set!)
(defelisp %--quit-char-set!               --quit-char-set!)
(defelisp %--set-ctag                     --set-ctag)
(defelisp %--timer-idleness-reset!        --timer-idleness-reset!)
(defelisp %--total-keys-set!              --total-keys-set!)
(defelisp %--recent-keys-index-set!       --recent-keys-index-set!)
(defelisp %--kbd-set-fetch-ptr-index      --kbd-set-fetch-ptr-index)
(defelisp %--kbd-set-store-ptr-index      --kbd-set-store-ptr-index)
(defelisp %--track-mouse-set!             --track-mouse-set!)
(defelisp %--input-pending-set!           --input-pending-set!)
(defelisp %--interrupt-input-blocked-set! --interrupt-input-blocked-set!)
(defelisp %--pending-signals-clear!       --pending-signals-clear!)
(defelisp %--set-internal-last-event-frame --set-internal-last-event-frame)

(define (init-keyboard!)
  ;; Mirrors the C body of init_keyboard (brief.org M27 imp-3 table) 1:1
  ;; and in C order.  A missed or reordered reset is a silent divergence
  ;; (Risk 2), not a build failure.
  ;; command_loop_level = -1;
  ((force %--command-loop-level-set!) -1)
  ;; quit_char = Ctl ('g');   (== 7)
  ((force %--quit-char-set!) 7)
  ;; Vunread_command_events = Qnil;   (elisp var)
  (set-symbol-value! 'unread-command-events #nil)
  ;; getctag = Qnil;
  ((force %--set-ctag) #nil)
  ;; last_command_event = Qnil;       (elisp var)
  (set-symbol-value! 'last-command-event #nil)
  ;; last_nonmenu_event = Qnil;       (elisp var)
  (set-symbol-value! 'last-nonmenu-event #nil)
  ;; last_input_event = Qnil;         (elisp var)
  (set-symbol-value! 'last-input-event #nil)
  ;; timer_idleness_start_time = invalid_timespec ();
  ((force %--timer-idleness-reset!))
  ;; total_keys = 0;
  ((force %--total-keys-set!) 0)
  ;; recent_keys_index = 0;
  ((force %--recent-keys-index-set!) 0)
  ;; kbd_fetch_ptr = kbd_buffer;
  ((force %--kbd-set-fetch-ptr-index) 0)
  ;; kbd_store_ptr = kbd_buffer;
  ((force %--kbd-set-store-ptr-index) 0)
  ;; track_mouse = Qnil;
  ((force %--track-mouse-set!) #nil)
  ;; input_pending = false;
  ((force %--input-pending-set!) #nil)
  ;; interrupt_input_blocked = 0;
  ((force %--interrupt-input-blocked-set!) 0)
  ;; pending_signals = false;
  ((force %--pending-signals-clear!))
  ;; Vlast_event_device = Qnil;       (elisp var)
  (set-symbol-value! 'last-event-device #nil)
  ;; internal_last_event_frame = Qnil;
  ((force %--set-internal-last-event-frame) #nil)
  ;; Vlast_event_frame = internal_last_event_frame;   (now nil) (elisp var)
  (set-symbol-value! 'last-event-frame #nil))
