;;; test-m18-bodies.scm --- M18 imp-2 test corpus for the Scheme echo
;;; bodies in (emacs echo), ports of C echo_keystrokes_p, echo_add_key,
;;; echo_dash, echo_update, echo_now, echo_length, echo_truncate
;;; (src/keyboard.c), plus the private echo-help-char-p (help_char_p's
;;; logic).
;;;
;;; Sourced by test/keyboard/test-m18-bodies.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback from
;;; elisp.  See docs/m18-plan.org §imp-2 and brief.org.
;;;
;;; Runs in the loadup-ERT harness.  Two elisp helpers that the ports
;;; legitimately call are stubbed here via set-symbol-function! (restored
;;; by with-echo-state) so the echo logic is exercised deterministically:
;;; the echo-prefix reader `internal-echo-keystrokes-prefix' (echo-update)
;;; and the keystroke-help appender `help--append-keystrokes-help'
;;; (echo-dash).  echo-help-char-p is private (not #:exported) so it is
;;; reached through module-ref on (emacs echo).
;;;
;;; Every sub-test that mutates the kboard echo-string/prompt, the
;;; immediate-echo bit, this-command-keys, or the guarded elisp vars
;;; (echo-keystrokes, echo-keystrokes-help, help-char, help-event-list,
;;; quit-flag) runs inside a with-echo-state dynamic-wind that resets and
;;; restores them, so the checks stay deterministic.

(use-modules (emacs echo))
(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))

;; NB: do NOT `use-module (emacs text-properties)' here — loading that
;; module in the shared loadup-emacs process breaks a later corpus's
;; (emacs kbd-buffer) resolution (wrong-type-argument "module").  The
;; hint-string content is compared with elisp string= instead.

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (%sym name)
  (symbol-function name))

(define (truthy? x)
  (not (eq? x #nil)))

(define (no-error? thunk)
  (catch #t
    (lambda () (thunk) #t)
    (lambda (key . args) (list 'error key args))))

;;; --- Echo-state access helpers --------------------------------------
;;; The kboard's echo fields, immediate-echo bit, and this-command-keys
;;; are all C-owned; read/write them through the imp-1 shims and the
;;; M2 KBOARD_LISP_FIELD getter/setters.
(define (kb)         ((%sym 'current-kboard)))
(define (ges)        ((%sym 'kboard-echo-string) (kb)))
(define (ses v)      ((%sym 'set-kboard-echo-string) (kb) v))
(define (gprompt)    ((%sym 'kboard-echo-prompt) (kb)))
(define (sprompt v)  ((%sym 'set-kboard-echo-prompt) (kb) v))
(define (set-imm v)  ((%sym '--set-current-kboard-immediate-echo) v))
(define (imm-p)      ((%sym '--current-kboard-immediate-echo-p)))
(define (reset-keys!) ((%sym '--reset-this-command-keys)))
(define (add-key! k)  ((%sym '--add-command-key) k))

;;; Private helper, reached via module-ref (not #:exported).
(define echo-help-char-p
  (module-ref (resolve-module '(emacs echo)) 'echo-help-char-p))

;;; Run THUNK with a fresh echo state and restore everything afterwards.
;;; Stubs every elisp function this corpus shadows — the two elisp
;;; helpers (internal-echo-keystrokes-prefix, help--append-keystrokes-help)
;;; and the C shims it spies on (--set-echoing!, --message3-nolog,
;;; --waiting-for-input-p, --quit-throw-to-read-char,
;;; --truncate-echo-area) — restoring each to its saved value (which is
;;; #nil when the harness never defined it).  Without this the stubs
;;; would leak into later corpora in the shared randomized test process.
(define (with-echo-state thunk)
  (let ((saved-es  (ges))
        (saved-ep  (gprompt))
        (saved-imm (imm-p))
        (saved-ek  (symbol-value 'echo-keystrokes))
        (saved-ekh (symbol-value 'echo-keystrokes-help))
        (saved-hc  (symbol-value 'help-char))
        (saved-hel (symbol-value 'help-event-list))
        (saved-qf  (symbol-value 'quit-flag))
        (saved-ekp (symbol-function 'internal-echo-keystrokes-prefix))
        (saved-hah (symbol-function 'help--append-keystrokes-help))
        (saved-se  (symbol-function '--set-echoing!))
        (saved-m3  (symbol-function '--message3-nolog))
        (saved-wfi (symbol-function '--waiting-for-input-p))
        (saved-qt  (symbol-function '--quit-throw-to-read-char))
        (saved-ta  (symbol-function '--truncate-echo-area)))
    (dynamic-wind
      (lambda ()
        (ses #nil) (sprompt #nil) (set-imm #nil) (reset-keys!)
        (set-symbol-value! 'echo-keystrokes 0)
        (set-symbol-value! 'echo-keystrokes-help #nil)
        (set-symbol-value! 'help-char 8)      ; Ctl('H'), the standard default
        (set-symbol-value! 'help-event-list #nil)
        (set-symbol-value! 'quit-flag #nil))
      thunk
      (lambda ()
        (ses saved-es) (sprompt saved-ep) (set-imm saved-imm)
        (set-symbol-value! 'echo-keystrokes saved-ek)
        (set-symbol-value! 'echo-keystrokes-help saved-ekh)
        (set-symbol-value! 'help-char saved-hc)
        (set-symbol-value! 'help-event-list saved-hel)
        (set-symbol-value! 'quit-flag saved-qf)
        (set-symbol-function! 'internal-echo-keystrokes-prefix saved-ekp)
        (set-symbol-function! 'help--append-keystrokes-help saved-hah)
        (set-symbol-function! '--set-echoing! saved-se)
        (set-symbol-function! '--message3-nolog saved-m3)
        (set-symbol-function! '--waiting-for-input-p saved-wfi)
        (set-symbol-function! '--quit-throw-to-read-char saved-qt)
        (set-symbol-function! '--truncate-echo-area saved-ta)))))

;;; --- 1. Registration ------------------------------------------------
;;; Coexistence-only: each exported symbol resolves as a procedure in
;;; (emacs echo).  echo-help-char-p is private and is checked separately.
(define m18-mod (resolve-module '(emacs echo)))
(for-each (lambda (sym)
            (check (format #f "reg/~a" sym) #t
                   (procedure? (module-ref m18-mod sym))))
          '(echo-keystrokes-p echo-add-key echo-dash echo-update
            echo-now echo-length echo-truncate))
(check "reg/echo-help-char-p-private" #t
       (procedure? (module-ref m18-mod 'echo-help-char-p)))

;;; --- 2. echo-keystrokes-p ------------------------------------------
(with-echo-state
 (lambda ()
   (set-symbol-value! 'echo-keystrokes 1)
   (check "ek/fixnum1" #t (echo-keystrokes-p))
   (set-symbol-value! 'echo-keystrokes 0.5)
   (check "ek/float-positive" #t (echo-keystrokes-p))
   (set-symbol-value! 'echo-keystrokes 0)
   (check "ek/zero" #f (echo-keystrokes-p))
   (set-symbol-value! 'echo-keystrokes -3)
   (check "ek/negative" #f (echo-keystrokes-p))
   (set-symbol-value! 'echo-keystrokes #nil)
   (check "ek/nil" #f (echo-keystrokes-p))))

;;; --- 3. echo-help-char-p (private) ----------------------------------
(with-echo-state
 (lambda ()
   (set-symbol-value! 'help-char 63)
   (set-symbol-value! 'help-event-list #nil)
   (check "helpchar/help-char" #t (echo-help-char-p 63))
   (check "helpchar/other" #f (echo-help-char-p 90))
   (set-symbol-value! 'help-event-list (list 64 65))
   (check "helpchar/list-member-64" #t (echo-help-char-p 64))
   (check "helpchar/list-member-65" #t (echo-help-char-p 65))
   (check "helpchar/list-nonmember" #f (echo-help-char-p 90))))

;;; --- 4. echo-add-key ------------------------------------------------
(with-echo-state
 (lambda ()
   ;; fixnum path matches single-key-description.
   (ses #nil)
   (echo-add-key 97)
   (check "addkey/fixnum" "a" (ges))
   ;; symbol path matches symbol-name.
   (ses #nil)
   (echo-add-key 'f1)
   (check "addkey/symbol" "f1" (ges))
   ;; separator space is added only when the prior echo-string is
   ;; non-empty.
   (ses "x")
   (echo-add-key 97)
   (check "addkey/separator" "x a" (ges))
   ;; help-char hint + text properties only when prior echo-string was
   ;; empty AND the key is a help character.  The hint string carries
   ;; text properties (an emacs-string wrapper), so compare content with
   ;; elisp string= rather than plain equal?.
   (set-symbol-value! 'help-char 63)
   (set-symbol-value! 'help-event-list #nil)
   (ses #nil)
   (echo-add-key 63)
   (check "addkey/help-hint" #t
          ((%sym 'string=) "? (Type ? for further options, C-q for quick help)"
                           (ges)))
   (check "addkey/help-prop-?" 'help-key-binding
          ((%sym 'get-text-property) 8 'face (ges)))
   (check "addkey/help-prop-cq" 'help-key-binding
          ((%sym 'get-text-property) 31 'face (ges)))
   ;; non-help char: no hint, no properties.
   (ses #nil)
   (echo-add-key 97)
   (check "addkey/nonhelp-no-hint" "a" (ges))
   (check "addkey/nonhelp-no-prop" #nil
          ((%sym 'get-text-property) 0 'face (ges)))))

;;; --- 5. echo-dash ---------------------------------------------------
(with-echo-state
 (lambda ()
   ;; guard: nil echo-string -> unchanged.
   (ses #nil)
   (echo-dash)
   (check "dash/guard-nil" #nil (ges))
   ;; guard: not immediate-echo and empty string -> unchanged.
   (set-imm #nil)
   (ses "")
   (echo-dash)
   (check "dash/guard-nonimm-empty" "" (ges))
   ;; guard: echo-prompt same length as echo-string -> unchanged.
   (set-imm #t)
   (ses "xy")
   (sprompt "xy")
   (echo-dash)
   (check "dash/guard-prompt" "xy" (ges))
   ;; guard: already has a trailing dash -> unchanged.
   (ses "ab-")
   (sprompt #nil)
   (echo-dash)
   (check "dash/guard-dash" "ab-" (ges))
   ;; guard: keystroke-help suffix ("p)") with echo-keystrokes-help -> unchanged.
   (ses "abp)")
   (set-symbol-value! 'echo-keystrokes-help #t)
   (echo-dash)
   (check "dash/guard-keystroke-help" "abp)" (ges))
   ;; success path: appends `-' and runs echo-now.
   (ses "abc")
   (set-symbol-value! 'echo-keystrokes-help #nil)
   (echo-dash)
   (check "dash/success" "abc-" (ges))
   ;; success path with keystroke-help: calls help--append-keystrokes-help
   ;; on the dashed string.
   (set-symbol-function! 'help--append-keystrokes-help
                         (lambda (s) (string-append s "!")))
   (ses "abc")
   (set-symbol-value! 'echo-keystrokes-help #t)
   (echo-dash)
   (check "dash/success-helpappend" "abc-!" (ges))))

;;; --- 6. echo-update -------------------------------------------------
(with-echo-state
 (lambda ()
   (set-symbol-function! 'internal-echo-keystrokes-prefix
                         (lambda () #nil))
   (set-imm #t)
   (reset-keys!) (add-key! 97) (add-key! 98)
   (sprompt "P>")
   (echo-update)
   (check "update/prompt-only" "P> a b" (ges))
   (set-imm #t) (sprompt #nil) (reset-keys!) (add-key! 97) (add-key! 98)
   (set-symbol-function! 'internal-echo-keystrokes-prefix
                         (lambda () "PR:"))
   (echo-update)
   (check "update/prefix-only" "PR: a b" (ges))
   (set-imm #t) (sprompt "P>") (reset-keys!) (add-key! 97) (add-key! 98)
   (echo-update)
   (check "update/prompt-and-prefix" "P>PR: a b" (ges))
   ;; mouse-movement events are skipped.
   (set-imm #t) (sprompt #nil) (reset-keys!)
   (add-key! 97) (add-key! (list 'mouse-movement 'win 1 2)) (add-key! 98)
   (set-symbol-function! 'internal-echo-keystrokes-prefix
                         (lambda () #nil))
   (echo-update)
   (check "update/skip-mouse" "a b" (ges))))

;;; --- 7. echo-now ----------------------------------------------------
(with-echo-state
 (lambda ()
   (set-symbol-function! 'internal-echo-keystrokes-prefix
                         (lambda () #nil))
   ;; Spy on --set-echoing! and --message3-nolog.
   (let ((echoing-calls '()) (msg3-args '()))
     (set-symbol-function! '--set-echoing!
                           (lambda (v) (set! echoing-calls (cons v echoing-calls))))
     (set-symbol-function! '--message3-nolog
                           (lambda (s) (set! msg3-args (cons s msg3-args))))
     (set-imm #nil)
     (ses "hello")
     (echo-now)
     ;; immediate-echo flipped to true.
     (check "now/immediate-echo" #t (imm-p))
     ;; --set-echoing! is toggled true-then-false.  echo-now nests (it
     ;; runs echo-update + echo-dash, each of which calls echo-now again),
     ;; so the shim is called more than twice; check that #t was set at
     ;; least once and that the last call reset `echoing' to #nil.
     (check "now/echoing-then-not" #t
            (and (memq #t echoing-calls)
                 (memq #nil echoing-calls)
                 (eq? (car echoing-calls) #nil)))
     ;; --message3-nolog displayed the echo string.
     (check "now/message3-args" #t (pair? msg3-args)))
   ;; quit-throw guard: fires only when BOTH waiting-for-input and
   ;; quit-flag are set.  waiting-for-input is a C flag not settable
   ;; from Scheme, so stub the shims to exercise the guard directly
   ;; (setting quit-flag alone would trip the C QUIT in the real
   ;; message3-nolog, so --message3-nolog is kept spied here too).
   (let ((throw-calls '()))
     (set-symbol-function! '--waiting-for-input-p (lambda () #nil))
     (set-symbol-function! '--quit-throw-to-read-char
                           (lambda () (set! throw-calls (cons #t throw-calls))))
     (set-symbol-value! 'quit-flag 'quit)
     (set-imm #t) (ses "safe")
     (echo-now)
     (check "now/quit-only-one-flag" '() throw-calls))
   (let ((throw-calls '()))
     (set-symbol-function! '--waiting-for-input-p (lambda () #t))
     (set-symbol-function! '--quit-throw-to-read-char
                           (lambda () (set! throw-calls (cons #t throw-calls))))
     (set-symbol-value! 'quit-flag 'quit)
     (set-imm #t) (ses "safe")
     (echo-now)
     (check "now/quit-both-flags" #t (pair? throw-calls)))))

;;; --- 8. echo-length / echo-truncate ---------------------------------
(with-echo-state
 (lambda ()
   (ses "hello")
   (check "length/string" 5 (echo-length))
   (ses #nil)
   (check "length/nil" 0 (echo-length))
   ;; truncate shortens the string.
   (ses "hello world")
   (echo-truncate 5)
   (check "truncate/shortens" "hello" (ges))
   ;; truncate still calls --truncate-echo-area for a no-op.
   (let ((calls 0))
     (set-symbol-function! '--truncate-echo-area
                           (lambda (n) (set! calls (+ calls 1))))
     (ses "ab")
     (echo-truncate 5)
     (check "truncate/noop-still-calls" 1 calls))))
