;;; test-read-char.el --- M8a SRFI-64 suite

;; Same coverage as ertest-read-char.el, transcribed for the
;; test-framework.el / SRFI-64 harness.  Keep in sync.

(test-begin "read-char")

(defvar m8--test-rec nil)
(defvar m8-test-special-observed nil)

(defun m8-test-state-ref (field)
  (--rc-test-state-ref m8--test-rec field))

(defun m8-with-rc-state (bindings thunk)
  (let ((m8--test-rec (--make-rc-state)))
    (--rc-state-fresh! m8--test-rec)
    (dolist (binding bindings)
      (--rc-test-state-set! m8--test-rec (car binding) (cdr binding)))
    (--rc-test-with-state m8--test-rec thunk)))

(defun m8-test-special-command ()
  (interactive)
  (setq m8-test-special-observed last-input-event))

(defun m8-test-input-method-consumes (_c)
  nil)

(test-assert "helpers/make-rc-state"    (fboundp '--make-rc-state))
(test-assert "helpers/rc-state-fresh!"  (fboundp '--rc-state-fresh!))
(test-assert "helpers/rc-test-state-ref" (fboundp '--rc-test-state-ref))
(test-assert "helpers/rc-test-state-set!" (fboundp '--rc-test-state-set!))
(test-assert "helpers/rc-test-with-state" (fboundp '--rc-test-with-state))

(let ((s (--make-rc-state)))
  (test-assert "rc-state/constructs-non-nil" (not (null s)))
  (--rc-state-fresh! s)
  (test-assert "rc-state-fresh/runs" t))

;;;; M8c

(test-assert "helpers/rc-prologue-drain-unread"
             (fboundp '--rc-prologue-drain-unread))
(test-eq "drain/fall-through-at-idle"
         'fall-through (--rc-prologue-drain-unread!))

(let ((unread-post-input-method-events (list ?p))
      (unread-command-events nil)
      (unread-input-method-events nil))
  (m8-with-rc-state
   nil
   (lambda ()
     (test-eq "drain/unread-post-input-method result"
              'reread-first (--rc-prologue-drain-unread!))
     (test-eq "drain/unread-post-input-method c"
              ?p (m8-test-state-ref 'c))
     (test-eq "drain/unread-post-input-method reread"
              t (m8-test-state-ref 'reread))
     (test-nil "drain/unread-post-input-method queue"
               unread-post-input-method-events))))

(let ((unread-post-input-method-events nil)
      (unread-command-events (list (cons 'no-record ?n)))
      (unread-input-method-events nil))
  (m8-with-rc-state
   nil
   (lambda ()
     (test-eq "drain/no-record command result"
              'reread-for-input-method
              (--rc-prologue-drain-unread!))
     (test-eq "drain/no-record command c"
              ?n (m8-test-state-ref 'c))
     (test-eq "drain/no-record command recorded"
              t (m8-test-state-ref 'recorded))
     (test-eq "drain/no-record command reread"
              t (m8-test-state-ref 'reread))
     (test-nil "drain/no-record command queue"
               unread-command-events))))

;;;; M8d

(test-assert "helpers/rc-prologue-macro-or-switch-frame"
             (fboundp '--rc-prologue-macro-or-switch-frame))
(test-eq "macro-sf/fall-through-at-idle"
         'fall-through (--rc-prologue-macro-or-switch-frame!))

(let ((executing-kbd-macro "a")
      (executing-kbd-macro-index 0))
  (m8-with-rc-state
   nil
   (lambda ()
     (test-eq "macro/replays-next-string-event result"
              'from-macro (--rc-prologue-macro-or-switch-frame!))
     (test-eq "macro/replays-next-string-event c"
              ?a (m8-test-state-ref 'c))
     (test-eq "macro/replays-next-string-event index"
              1 executing-kbd-macro-index))))

;;;; M8e

(test-assert "helpers/rc-prologue-redisplay"
             (fboundp '--rc-prologue-redisplay))
(test-eq "redisplay/no-op-when-stack-empty"
         nil (--rc-prologue-redisplay!))

;;;; M8f

(test-assert "helpers/rc-prologue-echo-and-menu"
             (fboundp '--rc-prologue-echo-and-menu))
(test-eq "echo-menu/fall-through-at-idle"
         'fall-through (--rc-prologue-echo-and-menu!))

;;;; M8g

(test-assert "helpers/rc-prologue-idle-echo-autosave"
             (fboundp '--rc-prologue-idle-echo-autosave))
(test-eq "idle-echo-autosave/no-op-when-stack-empty"
         nil (--rc-prologue-idle-echo-autosave!))

;;;; M8h

(test-assert "helpers/rc-prologue-xmenu-and-idle-gc"
             (fboundp '--rc-prologue-xmenu-and-idle-gc))
(test-eq "xmenu-and-idle-gc/fall-through-at-idle"
         'fall-through (--rc-prologue-xmenu-and-idle-gc!))

;;;; M8i

(test-assert "helpers/rc-prologue-kboard-and-queues"
             (fboundp '--rc-prologue-kboard-and-queues))
(test-eq "kboard-and-queues/fall-through-at-idle"
         'fall-through (--rc-prologue-kboard-and-queues!))

(m8-with-rc-state
 nil
 (lambda ()
   (test-eq "kboard-and-queues/wrong-kboard-origin-missing"
            'return-wrong-kboard
            (--rc-prologue-kboard-and-queues!))))

(let ((unread-command-events (list (cons 'no-record ?u))))
  (m8-with-rc-state
   `((orig-kboard . ,(current-kboard)))
   (lambda ()
     (test-eq "kboard-and-queues/no-record result"
              'fall-through (--rc-prologue-kboard-and-queues!))
     (test-eq "kboard-and-queues/no-record c"
              ?u (m8-test-state-ref 'c))
     (test-eq "kboard-and-queues/no-record recorded"
              t (m8-test-state-ref 'recorded))
     (test-eq "kboard-and-queues/no-record reread"
              t (m8-test-state-ref 'reread))
     (test-nil "kboard-and-queues/no-record queue"
               unread-command-events))))

(let ((unread-command-events (list (cons t ?q))))
  (m8-with-rc-state
   `((orig-kboard . ,(current-kboard)))
   (lambda ()
     (test-eq "kboard-and-queues/qt-wrapper result"
              'fall-through (--rc-prologue-kboard-and-queues!))
     (test-eq "kboard-and-queues/qt-wrapper c"
              ?q (m8-test-state-ref 'c))
     (test-nil "kboard-and-queues/qt-wrapper recorded"
               (m8-test-state-ref 'recorded))
     (test-nil "kboard-and-queues/qt-wrapper reread"
               (m8-test-state-ref 'reread))
     (test-nil "kboard-and-queues/qt-wrapper queue"
               unread-command-events))))

;;;; M8j

(test-assert "helpers/rc-wrong-kboard-and-non-reread"
             (fboundp '--rc-wrong-kboard-and-non-reread))
(test-eq "wkbd-nr/fall-through-at-idle"
         'fall-through (--rc-wrong-kboard-and-non-reread!))

;;;; M8k

(test-assert "helpers/rc-bufferp-and-special-event-map"
             (fboundp '--rc-bufferp-and-special-event-map))
(test-eq "bufp-special/fall-through-at-idle"
         'fall-through (--rc-bufferp-and-special-event-map!))

(m8-with-rc-state
 `((c . ,(current-buffer)))
 (lambda ()
   (test-eq "bufp-special/buffer-event-goes-to-exit"
            'goto-exit (--rc-bufferp-and-special-event-map!))))

(let ((special-event-map (make-sparse-keymap))
      (while-no-input-ignore-events nil)
      (last-input-event nil)
      (m8-test-special-observed nil))
  (define-key special-event-map [m8-test-special]
    'm8-test-special-command)
  (m8-with-rc-state
   '((c . m8-test-special))
   (lambda ()
     (test-eq "bufp-special/dispatch result"
              'goto-retry (--rc-bufferp-and-special-event-map!))
     (test-eq "bufp-special/dispatch observed"
              'm8-test-special m8-test-special-observed)
     (test-eq "bufp-special/dispatch last-input-event"
              'm8-test-special last-input-event)
     (test-eq "bufp-special/dispatch c"
              'm8-test-special (m8-test-state-ref 'c)))))

;;;; M8l

(test-assert "helpers/rc-event-translate-and-record"
             (fboundp '--rc-event-translate-and-record))
(test-eq "translate-record/fall-through-at-idle"
         'fall-through (--rc-event-translate-and-record!))

(m8-with-rc-state
 '((c . -1))
 (lambda ()
   (test-eq "translate-record/eof-goes-to-exit"
            'goto-exit (--rc-event-translate-and-record!))))

(let ((input-method-function #'ignore)
      (input-method-previous-message nil))
  (m8-with-rc-state
   '((c . ?z))
   (lambda ()
     (test-eq "translate-record/printable-input-method result"
              'fall-through (--rc-event-translate-and-record!))
     (test-eq "translate-record/printable-input-method recorded"
              t (m8-test-state-ref 'recorded))
     (test-eq "translate-record/printable-input-method c"
              ?z (m8-test-state-ref 'c)))))

;;;; M8m

(test-assert "helpers/rc-input-method-dispatch"
             (fboundp '--rc-input-method-dispatch))
(test-eq "input-method/fall-through-at-idle"
         'fall-through (--rc-input-method-dispatch!))

(let ((input-method-function (lambda (_c) (list ?x ?y ?z)))
      (unread-post-input-method-events nil))
  (m8-with-rc-state
   '((c . ?a))
   (lambda ()
     (test-eq "input-method/installs-returned-events result"
              'fall-through (--rc-input-method-dispatch!))
     (test-eq "input-method/installs-returned-events c"
              ?x (m8-test-state-ref 'c))
     (test-equal "input-method/installs-returned-events unread"
                 (list ?y ?z) unread-post-input-method-events)
     (test-eq "input-method/installs-returned-events recorded"
              t (m8-test-state-ref 'recorded)))))

(let ((input-method-function 'm8-test-input-method-consumes)
      (unread-post-input-method-events nil))
  (m8-with-rc-state
   '((c . ?a))
   (lambda ()
     (test-eq "input-method/retries-when-consumed result"
              'goto-retry (--rc-input-method-dispatch!))
     (test-eq "input-method/retries-when-consumed c"
              ?a (m8-test-state-ref 'c))
     (test-nil "input-method/retries-when-consumed recorded"
               (m8-test-state-ref 'recorded))
     (test-nil "input-method/retries-when-consumed unread"
               unread-post-input-method-events))))

;;;; M8n

(test-assert "helpers/rc-help-echo-and-help-form"
             (fboundp '--rc-help-echo-and-help-form))
(test-eq "help-echo-form/fall-through-at-idle"
         'fall-through (--rc-help-echo-and-help-form!))

(let ((help-form nil)
      (last-input-event nil))
  (unwind-protect
      (progn
        (clear-this-command-keys)
        (m8-with-rc-state
         '((c . ?r))
         (lambda ()
           (test-eq "help-echo-form/records-command-key result"
                    'fall-through (--rc-help-echo-and-help-form!))
           (test-eq "help-echo-form/records-command-key last-input-event"
                    ?r last-input-event)
           (test-equal "help-echo-form/records-command-key vector"
                       "r" (this-command-keys-vector)))))
    (clear-this-command-keys)))

;;;; M8final

(test-assert "helpers/rc-exit"         (fboundp '--rc-exit))
(test-assert "helpers/read-char-main"  (fboundp '--read-char-main))
(test-eq "rc-exit/nil-at-idle" nil (--rc-exit!))

;;;; Step 1 of state-to-record migration

(test-assert "helpers/rc-record" (fboundp '--rc-record))
(test-eq "rc-record/nil-at-idle" nil (--rc-record))

(test-end)
