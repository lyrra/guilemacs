;;; tty-modes.scm --- M43 imp-2: the TTY terminal-mode leaves
;;;                     ((emacs tty-modes))
;;;
;;; Thin Scheme wrappers over the two typed C termios leaves in
;;; src/sysdep.c and the --tty-fd accessor in src/keyboard.c:
;;;
;;;   (tty-fd terminal)            -> a plain int fd, or -1
;;;   (tty-get-mode fd)            -> (iflag oflag cflag lflag c_cc) or #f
;;;   (tty-set-mode fd mode flush?) -> 0 on success, else the negated errno
;;;
;;; fd is a plain int and the mode is a plain value list, so no struct,
;;; no FILE *, and no Lisp_Object crosses the termios layer (the M42
;;; rule).  C keeps the retry loop, the EINTR retry, the TCSAFLUSH /
;;; TCSADRAIN choice, the FLUSHP arm, the read-back compare, and the
;;; POSIX error mapping.
;;;
;;; imp-2 adds no policy here.  imp-3 (init_sys_modes) and imp-4
;;; (reset_sys_modes) compute the wanted mode in Scheme and call these
;;; leaves.  The wrappers stay thin and exported for those imps.  See
;;; brief.org M43 imp-2 sections 5 and 6.
;;;
;;; Conventions (identical to M9-M42): defelisp delayed references for
;;; every C DEFUN ((force %--foo)); elisp nil is #nil.

(define-module (emacs tty-modes)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (tty-fd tty-get-mode tty-set-mode))

;; The C leaves (src/keyboard.c and src/sysdep.c).
(defelisp %--tty-fd       --tty-fd)
(defelisp %--tty-get-mode --tty-get-mode)
(defelisp %--tty-set-mode --tty-set-mode)

;; Map a terminal object to its plain int input descriptor, or -1 when
;; it does not decode to a tty.
(define (tty-fd terminal)
  ((force %--tty-fd) terminal))

;; Read the terminal mode on the plain int FD as a plain value list, or
;; #f when the read fails.
(define (tty-get-mode fd)
  ((force %--tty-get-mode) fd))

;; Write the terminal mode MODE on the plain int FD.  When FLUSH? is
;; true, discard pending input.  Returns 0 on success, else a negative
;; fixnum holding the negated errno.
(define (tty-set-mode fd mode flush?)
  ((force %--tty-set-mode) fd mode flush?))
