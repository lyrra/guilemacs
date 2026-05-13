(define-module (emacs kboard)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (with-kboard init-kboard-registrations))

;;; M2 — KBOARD foreign-object wrapper for the keyboard.c → Guile port.
;;;
;;; The smob type and its 40 accessor DEFUNs are defined in C
;;; (src/guile.c + src/keyboard.c) and registered as elisp functions
;;; via SCM_SNARF_INIT at startup.  Elisp callers reach them by name
;;; directly.  Scheme callers (this module) reach them through
;;; symbol-function lookup.
;;;
;;; Exported elisp procedures (all defined in C):
;;;   kboardp, kboard-eq
;;;   current-kboard, set-current-kboard
;;;   kboard-<field> / set-kboard-<field>  for 18 Lisp fields:
;;;     overriding-terminal-local-map, last-command, real-last-command,
;;;     keyboard-translate-table, last-repeatable-command, prefix-arg,
;;;     last-prefix-arg, kbd-queue, defining-kbd-macro, last-kbd-macro,
;;;     system-key-alist, system-key-syms, window-system,
;;;     local-function-key-map, input-decode-map,
;;;     default-minibuffer-frame, echo-string, echo-prompt
;;;
;;; The KVAR(kb, field) C macro stays as the C-side lvalue interface;
;;; the Scheme accessors are for new code on this side of the
;;; boundary.  See docs/keyboard.org §M2.

(define (with-kboard kb thunk)
  "Run THUNK with KB as the current KBOARD; restore the previous
   current-kboard on any unwind (including abort-to-prompt)."
  (let ((current   (symbol-function 'current-kboard))
        (set-curr! (symbol-function 'set-current-kboard)))
    (let ((saved (current)))
      (dynamic-wind
        (lambda () (set-curr! kb))
        thunk
        (lambda () (set-curr! saved))))))

(define (init-kboard-registrations)
  "Wire with-kboard into the elisp symbol table."
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `((with-kboard ,with-kboard))))
