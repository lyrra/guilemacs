;;; test-m27-init-keyboard.scm --- M27 imp-3 (emacs keyboard-init) test
;;;   corpus.
;;;
;;; Covers the M27 imp-3 cutover (brief.org M27 imp-3): the 19
;;; file-static resets of init_keyboard moved out of src/keyboard.c into
;;; (emacs keyboard-init) as init-keyboard!.  The C dispatcher keeps
;;; only the current-kboard re-init, the sigaction installs and the
;;; signal / poll arms.  This corpus exercises init-keyboard! over
;;; stubbed setters:
;;;
;;;   - each of the 13 C cells receives its reset value from the brief
;;;     table, through its C shim;
;;;   - the 6 elisp variables are reset via set-symbol-value! 'NAME #nil;
;;;   - every reset fires exactly once and in C order (a missed or
;;;     reordered reset is a silent divergence, Risk 2 — the full-order
;;;     check below is the guard);
;;;   - init-keyboard! is an exported procedure (the C dispatcher's
;;;     scm_c_public_ref target).
;;;
;;; keyboard-init.scm references its C primitives through defelisp
;;; delays ((force %...)), so those delays are stubbed by replacing them
;;; inside the (emacs keyboard-init) module (module-set!), and the
;;; imported set-symbol-value! binding is stubbed the same way to record
;;; the (symbol . value) resets.  Every stub is restored in a
;;; dynamic-wind unwind, so nothing leaks into later corpora.
;;;
;;; Sourced by test/keyboard/test-m27-init-keyboard.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback from
;;; elisp.  See brief.org M27 imp-3.
;;;
;;; Live boot verification of the reset values (the imp-3 exit
;;; criterion) runs at startup in a normal build and is exercised by the
;;; whole live test harness; the sigaction installs cannot be SIGINT'd
;;; in this sandbox and are recorded unverified per the imp-2 precedent.

(use-modules (emacs keyboard-init))
(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

;;; --- Stub helpers ----------------------------------------------------

(define ki-mod (resolve-module '(emacs keyboard-init)))

;; The 13 C-shim defelisp delay variables, each paired with the call tag
;; its recording stub logs under (== the shim's Lisp name).
(define c-delay-vars
  '((%--command-loop-level-set!       . --command-loop-level-set!)
    (%--quit-char-set!                . --quit-char-set!)
    (%--set-ctag                      . --set-ctag)
    (%--timer-idleness-reset!         . --timer-idleness-reset!)
    (%--total-keys-set!               . --total-keys-set!)
    (%--recent-keys-index-set!        . --recent-keys-index-set!)
    (%--kbd-set-fetch-ptr-index       . --kbd-set-fetch-ptr-index)
    (%--kbd-set-store-ptr-index       . --kbd-set-store-ptr-index)
    (%--track-mouse-set!              . --track-mouse-set!)
    (%--input-pending-set!            . --input-pending-set!)
    (%--interrupt-input-blocked-set!  . --interrupt-input-blocked-set!)
    (%--pending-signals-clear!        . --pending-signals-clear!)
    (%--set-internal-last-event-frame . --set-internal-last-event-frame)))

;; Run THUNK (receiving LOG, a list of (TAG . ARGS) entries in call
;; order) with every (emacs keyboard-init) C delay and its
;; set-symbol-value! use replaced by a recording stub.  Restores all
;; afterwards.
(define (run-with-fakes! thunk)
  (let ((log '())
        (saved-delays (map (lambda (cell) (module-ref ki-mod (car cell)))
                           c-delay-vars))
        (saved-ssval (module-ref ki-mod 'set-symbol-value!)))
    (define (note name . args) (set! log (cons (cons name args) log)))
    (define (mk-stub tag)
      (lambda args (apply note tag args) #nil))
    (dynamic-wind
      (lambda ()
        ;; Stub the 13 defelisp C delays with recording procedures.
        (for-each
         (lambda (cell)
           (module-set! ki-mod (car cell) (delay (mk-stub (cdr cell)))))
         c-delay-vars)
        ;; Stub the imported set-symbol-value! to record (symbol value).
        (module-set! ki-mod 'set-symbol-value!
                     (lambda (sym val)
                       (note 'set-symbol-value! sym val)
                       #nil)))
      (lambda ()
        (init-keyboard!)
        (thunk (reverse log)))
      (lambda ()
        (let loop ((cells c-delay-vars) (saved saved-delays))
          (unless (null? cells)
            (module-set! ki-mod (car (car cells)) (car saved))
            (loop (cdr cells) (cdr saved))))
        (module-set! ki-mod 'set-symbol-value! saved-ssval)))))

;; The full expected reset sequence from brief.org M27 imp-3, in C order
;; (Risk 2: Vlast_event_frame must follow internal_last_event_frame's
;; nil write).
(define expected-order
  '((--command-loop-level-set! -1)
    (--quit-char-set! 7)
    (set-symbol-value! unread-command-events #nil)
    (--set-ctag #nil)
    (set-symbol-value! last-command-event #nil)
    (set-symbol-value! last-nonmenu-event #nil)
    (set-symbol-value! last-input-event #nil)
    (--timer-idleness-reset!)
    (--total-keys-set! 0)
    (--recent-keys-index-set! 0)
    (--kbd-set-fetch-ptr-index 0)
    (--kbd-set-store-ptr-index 0)
    (--track-mouse-set! #nil)
    (--input-pending-set! #nil)
    (--interrupt-input-blocked-set! 0)
    (--pending-signals-clear!)
    (set-symbol-value! last-event-device #nil)
    (--set-internal-last-event-frame #nil)
    (set-symbol-value! last-event-frame #nil)))

(define elisp-var-symbols
  '(unread-command-events last-command-event last-nonmenu-event
    last-input-event last-event-device last-event-frame))

;;; --- 1. Full reset sequence, in C order ------------------------------

(run-with-fakes!
 (lambda (log)
   (check "m27-init-keyboard!/full-c-order-sequence"
          expected-order log)))

;;; --- 2. Each reset fires once with the right value -------------------

(run-with-fakes!
 (lambda (log)
   ;; Pair expected-order with the actual log positionally: set-symbol-value!
   ;; fires three times under one tag, so assq (first match) is wrong here.
   (let ((zipped (map cons expected-order log)))
     (let loop ((i 0) (rest zipped))
       (unless (null? rest)
         (let* ((pair (car rest))
                (tag (car (car pair))))
           (check (format #f "m27-init-keyboard!/entry-~d-~a" i tag)
                  (car pair)
                  (cdr pair)))
         (loop (1+ i) (cdr rest)))))))

;;; --- 3. set-symbol-value! coverage -----------------------------------

(run-with-fakes!
 (lambda (log)
   (let* ((ssv (filter (lambda (e) (eq? (car e) 'set-symbol-value!)) log))
          (alist (map (lambda (e) (cons (cadr e) (caddr e))) ssv)))
     (check "m27-init-keyboard!/six-elisp-var-resets"
            6
            (length ssv))
     (for-each
      (lambda (sym)
        (let ((val (and (assq sym alist) (cdr (assq sym alist)))))
          (check (string-append "m27-init-keyboard!/elisp-var-" (symbol->string sym))
                 #nil
                 val)))
      elisp-var-symbols))))

;;; --- 4. Export -------------------------------------------------------

;; The C dispatcher resolves init-keyboard! via scm_c_public_ref; verify
;; it is an exported procedure of the module.
(check "m27-init-keyboard!/exported-init-keyboard!" #t
       (procedure? (module-ref (resolve-interface '(emacs keyboard-init))
                               'init-keyboard!)))
