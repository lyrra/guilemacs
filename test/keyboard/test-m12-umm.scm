;;; test-m12-umm.scm --- M12 imp-1 test corpus for the used-mouse-menu flag
;;;
;;; Sourced by test/keyboard/test-m12-umm.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp — Scheme format output does not reach emacs --batch
;;; stdout.
;;;
;;; Covers the three flag-setting sites of brief.org (M12 imp-1):
;;;   - main-queue install path (rc-read-and-install-event!): stub
;;;     %read-decoded-event-from-main-queue to return a non-nil second
;;;     value (the used-mouse-menu pointer), and a nil one (negative).
;;;   - X-menu read block (rc-prologue-xmenu-and-idle-gc!): stub
;;;     %rc-read-char-x-menu-prompt to return (values EVENT #t) / #f
;;;     and drive the real block with the gate satisfied.
;;;   - the C DEFUN --rc-read-char-x-menu-prompt two-value contract:
;;;     with a live rec and a nil prev-event (read_char_x_menu_prompt
;;;     returns Qnil without blocking), it must return exactly two
;;;     values with the flag read back as #f (M12 imp-3 deleted the
;;;     used-mouse-menu pointer slot, so only the local-bool path is
;;;     left).
;;; Plus the M12 imp-2 two-value contract:
;;;   - rc-exit! returns (EVENT FLAG) / (#nil #f) on an empty stack.
;;;   - all three wrong-kboard -2 exits of read-char-main return
;;;     (values -2 FLAG) with the live flag, so the value path never
;;;     drops a flag the pointer path already wrote.
;;;
;;; Stubbing (with-read-char-stubs below) only takes effect while
;;; (emacs read-char) is loaded INTERPRETED.  The harness runs with
;;; HOME=/nonexistent, so Guile auto-compile fails and the module is
;;; interpreted (verified by probe; the fix.org compiled-.go trap does
;;; not apply here).
(use-modules (emacs elisp-ref))      ; %c

(define (%c name) (symbol-function name))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (truthy? x)
  (not (eq? x #nil)))

;; Run THUNK (a section of the corpus) and turn any error into a
;; reported FAIL (key + first arg only — the full args can be
;; unprintable and crash the pre-unwind backtrace printer).
(define (run-section name thunk)
  (catch #t
    (lambda ()
      (thunk)
      (report name 'PASS))
    (lambda (k . args)
      (report name (list 'ERROR k (if (pair? args) (car args) args))))))

(define (make-test-rec)
  (let ((rec ((%c '--make-rc-state))))
    ((%c '--rc-state-fresh!) rec)
    rec))

(define (rec-field rec field)
  ((%c '--rc-test-state-ref) rec field))

;; Rebind top-level variables inside (emacs read-char) for the
;; duration of THUNK, then restore.  ENTRIES are (NAME . PROC); the
;; variable is set to (delay PROC) when it currently holds a promise
;; (the %foo delayed-ref pattern), or to PROC directly for plain
;; top-level procedures (e.g. %interactive?).
(define (with-read-char-stubs stubs thunk)
  (let* ((mod (resolve-module '(emacs read-char)))
         (saved
          (map (lambda (entry)
                 (let ((var (module-variable mod (car entry))))
                   (cons var (variable-ref var))))
               stubs)))
    (dynamic-wind
      (lambda ()
        (for-each (lambda (entry)
                    (let ((var (module-variable mod (car entry))))
                      (variable-set! var
                                     (if (promise? (variable-ref var))
                                         (delay (cdr entry))
                                         (cdr entry)))))
                  stubs))
      thunk
      (lambda ()
        (for-each (lambda (entry)
                    (variable-set! (car entry) (cdr entry)))
                  saved)))))

;;; --- 1. main-queue install path (rc-read-and-install-event!) -------

;; Stub %read-decoded-event-from-main-queue returning a NON-nil second
;; value: the pointer path fires and the flag must be set.
(run-section
 "main-queue/non-nil-umm"
 (lambda ()
   (with-read-char-stubs
    `((%read-decoded-event-from-main-queue
       . ,(lambda (end-time tag prev-event)
            (values 'm8-menu-event 'umm-non-nil))))
    (lambda ()
      (let ((rec (make-test-rec)))
        ((%c '--rc-test-with-state)
         rec
         (lambda () ((%c '--rc-read-and-install-event!))))
        (check "main-queue/flag-set-on-non-nil-umm" #t
               (truthy? (rec-field rec 'used-mouse-menu-flag)))
        (check "main-queue/event-installed" 'm8-menu-event
               (rec-field rec 'c)))))))

;; Stub returning a nil second value: the pointer path does not fire
;; and the flag must stay false.
(run-section
 "main-queue/nil-umm"
 (lambda ()
   (with-read-char-stubs
    `((%read-decoded-event-from-main-queue
       . ,(lambda (end-time tag prev-event)
            (values 'm8-plain-event #nil))))
    (lambda ()
      (let ((rec (make-test-rec)))
        ((%c '--rc-test-with-state)
         rec
         (lambda () ((%c '--rc-read-and-install-event!))))
        (check "main-queue/flag-false-on-nil-umm" #f
               (rec-field rec 'used-mouse-menu-flag))
        (check "main-queue/nil-umm-event-installed" 'm8-plain-event
               (rec-field rec 'c)))))))

;;; --- 2. X-menu read block (rc-prologue-xmenu-and-idle-gc!) ---------

;; Drive the real block with the gate satisfied and the prompt stub
;; returning a truthy second value: the flag must be set and the event
;; installed into c.
(define (run-xmenu-block stub-prompt)
  (with-read-char-stubs
   `((%rc-read-char-x-menu-prompt . ,(lambda () (values 'm8-xmenu-event stub-prompt)))
     (%interactive? . ,(lambda () #t)))
   (lambda ()
     (let* ((rec (make-test-rec))
            (map ((%c 'make-sparse-keymap)))
            (saved-unread (symbol-value 'unread-command-events)))
       (dynamic-wind
         (lambda ()
           ((%c '--rc-test-state-set!) rec 'map map)
           ((%c '--rc-test-state-set!) rec 'prev-event (cons 'm8-cmd 'm8-param))
           ;; Non-nil end-time so the block skips the idle-timer stop.
           ((%c '--rc-test-state-set!) rec 'end-time 'm8-not-timed)
           (set-symbol-value! 'unread-command-events #nil))
         (lambda ()
           ((%c '--rc-test-with-state)
            rec
            (lambda () ((%c '--rc-prologue-xmenu-and-idle-gc!)))))
         (lambda ()
           (set-symbol-value! 'unread-command-events saved-unread)))
       (list (rec-field rec 'c) (rec-field rec 'used-mouse-menu-flag))))))

(run-section
 "xmenu-block/menu-choice"
 (lambda ()
   (let ((result (run-xmenu-block #t)))
     (check "xmenu-block/flag-set-on-menu-choice" '(m8-xmenu-event #t) result))))

(run-section
 "xmenu-block/no-menu-choice"
 (lambda ()
   (let ((result (run-xmenu-block #f)))
     (check "xmenu-block/flag-false-without-menu-choice"
            '(m8-xmenu-event #f) result))))

;;; --- 3. --rc-read-char-x-menu-prompt two-value contract ------------

;; Live rec and nil prev-event (read_char_x_menu_prompt returns Qnil
;; without blocking): the DEFUN must return exactly two values, the
;; flag read back from its local bool as #f (M12 imp-3 — the rec's
;; used-mouse-menu pointer field is gone).
(run-section
 "xmenu-defun/two-values"
 (lambda ()
   (let ((rec (make-test-rec)))
     ((%c '--rc-test-state-set!) rec 'prev-event #nil)
     ((%c '--rc-test-with-state)
      rec
      (lambda ()
        (call-with-values
            (lambda () ((%c '--rc-read-char-x-menu-prompt)))
          (lambda args
            (check "xmenu-defun/two-values" 2 (length args))
            (check "xmenu-defun/flag-false" #f (cadr args)))))))))

;;; --- 4. rc-exit! two-value contract (M12 imp-2) --------------------

;; Module access like with-read-char-stubs: call rc-exit! and
;; read-char-main directly via module-ref while (emacs read-char) is
;; loaded INTERPRETED.
(define rc-exit! (module-ref (resolve-module '(emacs read-char)) 'rc-exit!))
(define read-char-main
  (module-ref (resolve-module '(emacs read-char)) 'read-char-main))

;; Push a rec with c = EVENT and the flag pre-set; rc-exit! must
;; return (values EVENT FLAG).
(define (check-rc-exit flag)
  (let ((rec (make-test-rec)))
    ((%c '--rc-test-state-set!) rec 'c 'm8-exit-event)
    ((%c '--rc-test-state-set!) rec 'used-mouse-menu-flag flag)
    ((%c '--rc-test-with-state)
     rec
     (lambda ()
       (call-with-values rc-exit! list)))))

(run-section
 "rc-exit/flag-true"
 (lambda ()
   (check "rc-exit/two-values-flag-true"
          '(m8-exit-event #t) (check-rc-exit #t))))

(run-section
 "rc-exit/flag-false"
 (lambda ()
   (check "rc-exit/two-values-flag-false"
          '(m8-exit-event #f) (check-rc-exit #f))))

(run-section
 "rc-exit/no-rec"
 (lambda ()
   ;; Nothing pushed on the record stack: must yield (#nil #f), not a
   ;; single value.
   (check "rc-exit/two-values-no-rec"
          '(#nil #f) (call-with-values rc-exit! list))))

;;; --- 5. wrong-kboard -2 exits of read-char-main (M12 imp-2) --------

;; Drive read-char-main straight to one of its three wrong-kboard -2
;; exits.  STUBS route the prologue to the target site; the flag is
;; pre-set to #t so the value path must return (values -2 #t) — a
;; hard-coded #f here would fail (and Step 4's eassert would catch
;; the divergence from the pointer path).
(define (run-wrong-kboard stubs)
  (with-read-char-stubs
   stubs
   (lambda ()
     (let ((rec (make-test-rec)))
       ((%c '--rc-test-state-set!) rec 'used-mouse-menu-flag #t)
       ((%c '--rc-test-with-state)
        rec
        (lambda ()
          (call-with-values
              (lambda () (read-char-main #nil))
            list)))))))

(run-section
 "wrong-kboard/after-macro-sf"
 (lambda ()
   (let ((result
          (run-wrong-kboard
           `((rc-prologue-drain-unread! . ,(lambda () 'fall-through))
             (rc-prologue-macro-or-switch-frame! . ,(lambda () 'fall-through))
             (rc-prologue-echo-and-menu! . ,(lambda () 'return-wrong-kboard))))))
     (check "wrong-kboard/after-macro-sf-two-values" '(-2 #t) result))))

(run-section
 "wrong-kboard/after-xmenu"
 (lambda ()
   (let ((result
          (run-wrong-kboard
           `((rc-prologue-drain-unread! . ,(lambda () 'fall-through))
             (rc-prologue-macro-or-switch-frame! . ,(lambda () 'fall-through))
             (rc-prologue-echo-and-menu! . ,(lambda () 'fall-through))
             (rc-prologue-idle-echo-autosave! . ,(lambda () #nil))
             (rc-prologue-xmenu-and-idle-gc! . ,(lambda () 'fall-through))
             (rc-prologue-kboard-and-queues! . ,(lambda () 'return-wrong-kboard))))))
     (check "wrong-kboard/after-xmenu-two-values" '(-2 #t) result))))

(run-section
 "wrong-kboard/non-reread-section"
 (lambda ()
   (let ((result
          (run-wrong-kboard
           `((rc-prologue-drain-unread! . ,(lambda () 'fall-through))
             (rc-prologue-macro-or-switch-frame! . ,(lambda () 'fall-through))
             (rc-prologue-echo-and-menu! . ,(lambda () 'fall-through))
             (rc-prologue-idle-echo-autosave! . ,(lambda () #nil))
             (rc-prologue-xmenu-and-idle-gc! . ,(lambda () 'fall-through))
             (rc-prologue-kboard-and-queues! . ,(lambda () 'fall-through))
             (rc-wrong-kboard-and-non-reread! . ,(lambda () 'return-wrong-kboard))))))
     (check "wrong-kboard/non-reread-two-values" '(-2 #t) result))))

;;; --- 6. M12 imp-3: the pointer field is gone -----------------------

;; %rc-test-state-ref / %rc-test-state-set! fall through to their else
;; branch (an elisp error) for the deleted used-mouse-menu pointer
;; field, while the surviving -flag field still round-trips.  This
;; guards brief.org Step 3: the pointer field and its accessors must
;; stay deleted (M12 imp-3; the flag is the only path).
(run-section
 "imp3/pointer-field-gone"
 (lambda ()
   (let ((rec (make-test-rec)))
     (check "imp3/ref-errors-on-pointer-field"
            #t
            (catch #t
              (lambda ()
                ((%c '--rc-test-state-ref) rec 'used-mouse-menu)
                #f)
              (lambda (k . args) #t)))
     (check "imp3/set-errors-on-pointer-field"
            #t
            (catch #t
              (lambda ()
                ((%c '--rc-test-state-set!) rec 'used-mouse-menu #t)
                #f)
              (lambda (k . args) #t)))
     (check "imp3/flag-round-trips"
            #t
            (begin
              ((%c '--rc-test-state-set!) rec 'used-mouse-menu-flag #t)
              (truthy?
               ((%c '--rc-test-state-ref) rec 'used-mouse-menu-flag)))))))
