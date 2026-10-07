;;; emacs.scm --- the invocation / daemon boundary of src/emacs.c
;;;                ((emacs emacs))
;;;
;;; The invocation / daemon boundary of src/emacs.c has five blocks
;;; (docs/m50-plan.org section 3.1).  Four STAY in C; the daemonp block
;;; MOVES (milestone.org section 3).  M50 imp-2 added one typed C leaf,
;;; --emacs-daemon-state, and this thin wrapper.  M50 imp-3 will move
;;; the daemonp DECISION HERE; imp-2 moves no decision.
;;;
;;;   (emacs-daemon-state) -> the daemon facts as a *plain list*
;;;        (FLAG NAME).  FLAG is t when this process is a daemon, else
;;;        nil (#nil).  NAME is the daemon name as a plain string, or
;;;        nil (#nil).
;;;
;;; The C leaf returns Qt / Qnil.  Qnil reads as elisp nil, which is the
;;; Guile value #nil, NOT #f; the corpus probe asserts (eq flag nil).  A
;;; Scheme boolean false is a plain #f, but it is not the leaf's nil.
;;;
;;; imp-2 returns BOTH raw facts in one list, so imp-3 can compute the
;;; daemonp selection here without a second leaf cut.  The C decision of
;;; daemonp is then a plain composition: when FLAG is true, return NAME
;;; or t, else nil (#nil).
;;;
;;; Every value is plain: a boolean, a string, nil (#nil), or a list of
;;; plain values.  No Lisp_Object, char *, or struct crosses the layer
;;; (the M42 rule).  The mechanism (IS_DAEMON and daemon_name) stays in
;;; C (src/emacs.c emacs_daemon_state_1).  This module holds no FFI call
;;; and no scm_c_public_ref.
;;;
;;; Conventions (identical to M9-M49): #nil is elisp nil; no
;;; module-level mutable state.

(define-module (emacs emacs)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (emacs-daemon-state))

;; The one C leaf of the block (src/emacs.c).  It returns the raw facts
;; (FLAG NAME) as a plain list.
(defelisp %--emacs-daemon-state --emacs-daemon-state)

;; Return the daemon facts (FLAG NAME) as a plain list.  FLAG is t /
;; nil (#nil); NAME is a plain string or nil (#nil).  M50 imp-3 will
;; extend this wrapper with the daemonp selection.
(define (emacs-daemon-state)
  ((force %--emacs-daemon-state)))
