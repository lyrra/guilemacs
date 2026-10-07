;;; emacs.scm --- the invocation / daemon boundary of src/emacs.c
;;;                ((emacs emacs))
;;;
;;; The invocation / daemon boundary of src/emacs.c has five blocks
;;; (docs/m50-plan.org section 3.1).  Four STAY in C; the daemonp block
;;; MOVES (milestone.org section 3).  M50 imp-2 added one typed C leaf,
;;; --emacs-daemon-state, and its thin wrapper.  M50 imp-3 DELETES that
;;; leaf and moves the daemonp DECISION HERE.
;;;
;;;   (emacs-daemonp FLAG NAME) -> the daemonp selection.
;;;        When FLAG is true, return NAME if it is a string, else t.
;;;        Otherwise return nil (#nil).
;;;
;;; The C hub Fdaemonp reads the two plain facts with the C mechanism
;;; emacs_daemon_state_1 (the IS_DAEMON read and the daemon_name read),
;;; splits the plain list IN C, and calls this policy with the two plain
;;; values.  This is the whole decision of the old C block daemonp: when
;;; IS_DAEMON, return daemon_name as a string, else t, else nil.
;;;
;;; The C facts are Qt / Qnil.  Qnil reads as elisp nil (#nil), which is
;;; the Guile value #nil, NOT #f.  The corpus probe asserts (eq result
;;; nil).  A Scheme boolean false is a plain #f, but it is not the elisp
;;; nil, so the nil branch returns #nil, never #f.
;;;
;;; Every value is plain: a boolean, a string, or nil (#nil).  No
;;; Lisp_Object, char *, or struct crosses the layer (the M42 rule).
;;; The mechanism (IS_DAEMON and daemon_name) stays in C (src/emacs.c
;;; emacs_daemon_state_1).  This module holds no FFI call and no
;;; scm_c_public_ref.
;;;
;;; Conventions (identical to M9-M49): #nil is elisp nil; no
;;; module-level mutable state.

(define-module (emacs emacs)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (emacs-daemonp))

;; The daemonp selection of the block (src/emacs.c).  FLAG is a plain
;; boolean (true when IS_DAEMON); NAME is a plain string or nil (#nil).
;; Return the daemon name string, or t, or nil (#nil).  This is the
;; moved decision of M50 imp-3.
(define (emacs-daemonp flag name)
  (if flag
      (or name #t)
      #nil))
