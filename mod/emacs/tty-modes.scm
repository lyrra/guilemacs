;;; tty-modes.scm --- M43 imp-2/imp-3/imp-4: the TTY terminal-mode leaves,
;;;                     the init_sys_modes mode policy, and the
;;;                     reset_sys_modes / suppress_echo / flow-unlock
;;;                     policy ((emacs tty-modes))
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
;;; imp-2 adds no policy here.  imp-3 moves the mode policy of
;;; init_sys_modes (src/sysdep.c:1070) into Scheme:
;;;
;;;   (tty-mode-constants)      -> a plain key/value list of the termios
;;;                                flag names and c_cc indexes this build
;;;                                has (an absent name is absent)
;;;   (tty-mode-wanted base flags) -> the wanted 5-element mode list.
;;;                                PURE: it runs no syscall.  This is the
;;;                                primary proof of imp-3.
;;;   (init-tty-mode fd base flags) -> the wanted mode.  The thin entry
;;;                                point: it calls the pure policy and
;;;                                applies the result with tty-set-mode.
;;;
;;; The base mode is the mode C saved in tty_out->old_tty: C passes it
;;; as a plain 5-element list, so the mode is read once and no
;;; second-read proof is needed.  The flag list holds the plain inputs
;;; (flow-control? meta-key? controlling-tty? quit-char) plus the build
;;; constants (tty-mode-constants).  See brief.org M43 imp-3.
;;;
;;; Conventions (identical to M9-M42): defelisp delayed references for
;;; every C DEFUN ((force %--foo)); elisp nil is #nil.

(define-module (emacs tty-modes)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:use-module (rnrs bytevectors)     ; bytevector-length / bytevector-u8-ref
  #:declarative? #t
  #:export (tty-fd tty-get-mode tty-set-mode
            tty-mode-constants tty-mode-wanted init-tty-mode
            tty-mode-restore tty-mode-no-echo
            reset-tty-mode suppress-echo-tty unlock-tty-flow))

;; The C leaves (src/keyboard.c and src/sysdep.c).
(defelisp %--tty-fd       --tty-fd)
(defelisp %--tty-get-mode --tty-get-mode)
(defelisp %--tty-set-mode --tty-set-mode)
(defelisp %--tty-mode-constants --tty-mode-constants)
(defelisp %--tty-flow-unlock --tty-flow-unlock)

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

;;; --- The build constant table (brief.org section 8) -----------------

;; The termios flag names and c_cc indexes this build has, as a plain
;; key/value list.  An #ifdef arm is a build fact, so an absent name is
;; absent from the list.  C answers for this build; Scheme must not
;; hardcode a platform value.
;;
;; The list is build data and cannot change at run time, so memoize it in
;; a promise instead of crossing into C on every call.  init_sys_modes
;; runs at startup and at every resume for each tty (review cr.org F7);
;; a promise avoids a top-level set! in this declarative module.
(define constants-promise (delay ((force %--tty-mode-constants))))
(define (tty-mode-constants)
  (force constants-promise))

;; The key/value list is a flat plist (key value key value ...), the
;; elisp convention.  FLAG-CELL returns the tail of FLAGS that starts at
;; the value of NAME, or #f when NAME is absent.  A present name with a
;; false value is distinguishable from an absent name.
(define (flag-cell flags name)
  (let loop ((l flags))
    (cond
     ((or (null? l) (null? (cdr l))) #f)
     ((eq? (car l) name) (cdr l))
     (else (loop (cddr l))))))

(define (flag-ref flags name)
  (let ((cell (flag-cell flags name)))
    (if cell (car cell) #f)))

(define (flag-present? flags name)
  (and (flag-cell flags name) #t))

;;; --- The pure policy (brief.org section 5) --------------------------

;; Copy a bytevector.  (bytevector-copy) is not in scope here (the elisp
;; runtime import does not re-export it), so copy the bytes directly.
(define (bv-copy bv)
  (let* ((n (bytevector-length bv))
         (out (make-bytevector n 0)))
    (let loop ((i 0))
      (if (< i n)
          (begin (bytevector-u8-set! out i (bytevector-u8-ref bv i))
                 (loop (1+ i)))
          out))))

;; Compute the wanted terminal mode as a plain 5-element list
;; (iflag oflag cflag lflag c_cc).  BASE is the saved base mode list and
;; FLAGS is the plain key/value list of the plain inputs plus the build
;; constants.  This is the exact flag rule of init_sys_modes
;; (src/sysdep.c:1102-1241 at base 251d59045), with the dropped-platform
;; arms (AIX, MSDOS, HAIKU, DOS_NT) deleted.  It runs no syscall.
(define (tty-mode-wanted base flags)
  (let* ((iflag (list-ref base 0))
         (oflag (list-ref base 1))
         (cflag (list-ref base 2))
         (lflag (list-ref base 3))
         ;; Work on a copy of c_cc, so the caller's base mode is intact.
         (c_cc  (bv-copy (list-ref base 4)))
         (flow? (flag-ref flags 'flow-control?))
         (meta? (flag-ref flags 'meta-key?))
         (ctrl? (flag-ref flags 'controlling-tty?))
         (quit  (flag-ref flags 'quit-char)))
    ;; iflag: set IGNBRK; clear ICRNL, INLCR, ISTRIP.
    (set! iflag (logior iflag (flag-ref flags 'IGNBRK)))
    (set! iflag (logand iflag (lognot (flag-ref flags 'ICRNL))))
    (if (flag-present? flags 'INLCR)
        (set! iflag (logand iflag (lognot (flag-ref flags 'INLCR)))))
    (if (flag-present? flags 'ISTRIP)
        (set! iflag (logand iflag (lognot (flag-ref flags 'ISTRIP)))))
    ;; lflag: clear ECHO, ICANON, IEXTEN; set ISIG.
    (set! lflag (logand lflag (lognot (flag-ref flags 'ECHO))))
    (set! lflag (logand lflag (lognot (flag-ref flags 'ICANON))))
    (if (flag-present? flags 'IEXTEN)
        (set! lflag (logand lflag (lognot (flag-ref flags 'IEXTEN)))))
    (set! lflag (logior lflag (flag-ref flags 'ISIG)))
    ;; Flow control.
    (if flow?
        (begin
          (set! iflag (logior iflag (flag-ref flags 'IXON)))
          (if (flag-present? flags 'IXANY)
              (set! iflag (logand iflag (lognot (flag-ref flags 'IXANY))))))
        (set! iflag (logand iflag (lognot (flag-ref flags 'IXON)))))
    ;; oflag: clear ONLCR, TAB3.
    (set! oflag (logand oflag (lognot (flag-ref flags 'ONLCR))))
    (set! oflag (logand oflag (lognot (flag-ref flags 'TAB3))))
    ;; cflag: with CS8, set CS8 and clear PARENB when meta-key.
    (if (flag-present? flags 'CS8)
        (if meta?
            (begin
              (set! cflag (logior cflag (flag-ref flags 'CS8)))
              (set! cflag (logand cflag (lognot (flag-ref flags 'PARENB)))))))
    ;; c_cc: VMIN = 1, VTIME = 0.
    (bytevector-u8-set! c_cc (flag-ref flags 'VMIN) 1)
    (bytevector-u8-set! c_cc (flag-ref flags 'VTIME) 0)
    ;; c_cc: VINTR and VQUIT take quit-char on the controlling tty, else
    ;; CDISABLE.
    (if ctrl?
        (begin
          (bytevector-u8-set! c_cc (flag-ref flags 'VINTR) quit)
          (bytevector-u8-set! c_cc (flag-ref flags 'VQUIT) quit))
        (begin
          (bytevector-u8-set! c_cc (flag-ref flags 'VINTR)
                              (flag-ref flags 'CDISABLE))
          (bytevector-u8-set! c_cc (flag-ref flags 'VQUIT)
                              (flag-ref flags 'CDISABLE))))
    ;; c_cc: the shell-layering / editing characters are CDISABLE when
    ;; the build has them.
    (for-each
     (lambda (name)
       (if (flag-present? flags name)
           (bytevector-u8-set! c_cc (flag-ref flags name)
                               (flag-ref flags 'CDISABLE))))
     '(VSWTCH VSUSP V_DSUSP VDSUSP VLNEXT VREPRINT VWERASE VDISCARD))
    ;; c_cc: VSTART / VSTOP when flow control is on, else CDISABLE.
    (if flow?
        (begin
          (if (flag-present? flags 'VSTART)
              (bytevector-u8-set! c_cc (flag-ref flags 'VSTART) #o21))
          (if (flag-present? flags 'VSTOP)
              (bytevector-u8-set! c_cc (flag-ref flags 'VSTOP) #o23)))
        (begin
          (if (flag-present? flags 'VSTART)
              (bytevector-u8-set! c_cc (flag-ref flags 'VSTART)
                                  (flag-ref flags 'CDISABLE)))
          (if (flag-present? flags 'VSTOP)
              (bytevector-u8-set! c_cc (flag-ref flags 'VSTOP)
                                  (flag-ref flags 'CDISABLE)))))
    (list iflag oflag cflag lflag c_cc)))

;;; --- The restore and no-echo rules (brief.org section 5.1, 5.2) -----

;; The reset_sys_modes restore rule.  The whole saved mode returns, so no
;; flag changes: return a *fresh* list and a *fresh* copy of c_cc, so the
;; caller's saved base mode stays intact.  A platform difference gets a
;; typed arm here later, not a Scheme branch on the OS name.  Runs no
;; syscall.
(define (tty-mode-restore base)
  (list (list-ref base 0)
        (list-ref base 1)
        (list-ref base 2)
        (list-ref base 3)
        (bv-copy (list-ref base 4))))

;; The suppress_echo_on_tty rule.  Copy BASE; clear ICANON and ECHO in the
;; lflag word.  The dropped-platform DOS_NT arm (set the whole mode to
;; zero) is deleted.  Runs no syscall.
(define (tty-mode-no-echo base flags)
  (let* ((iflag (list-ref base 0))
         (oflag (list-ref base 1))
         (cflag (list-ref base 2))
         (lflag (list-ref base 3))
         (c_cc  (bv-copy (list-ref base 4))))
    (set! lflag (logand lflag (lognot (flag-ref flags 'ICANON))))
    (set! lflag (logand lflag (lognot (flag-ref flags 'ECHO))))
    (list iflag oflag cflag lflag c_cc)))

;;; --- The thin entry point (brief.org section 7) ---------------------

;; Compute the wanted mode from BASE and the plain inputs FLAGS, and
;; apply it with the imp-2 leaf.  FLAGS holds the plain inputs
;; (flow-control? meta-key? controlling-tty? quit-char); the build
;; constants are merged in here.  C keeps the guards and the post-set
;; work.  Returns the wanted mode list.
(define (init-tty-mode fd base flags)
  (let* ((full (append flags (tty-mode-constants)))
         (wanted (tty-mode-wanted base full)))
    (tty-set-mode fd wanted #f)
    wanted))

;;; --- The restore / no-echo / flow-unlock entry points (brief.org §6) -

;; Restore the saved mode BASE on FD (the reset_sys_modes entry).  C
;; passes the saved tty_out->old_tty as a plain 5-element list, or #f
;; (elisp nil) when old_tty is NULL.  Return the leaf status, or #f when
;; there is nothing to do.  The retry loop stays in the C leaf.
(define (reset-tty-mode fd base)
  (if base
      (tty-set-mode fd (tty-mode-restore base) #f)
      #f))

;; Clear ICANON and ECHO on FD (the suppress_echo_on_tty entry).  Read the
;; mode first; when the read fails (#f), return #f.  Else apply the
;; tty-mode-no-echo rule.
(define (suppress-echo-tty fd)
  (let ((mode (tty-get-mode fd)))
    (if mode
        (tty-set-mode fd (tty-mode-no-echo mode (tty-mode-constants)) #f)
        #f)))

;; Unlock the terminal flow control on FD (the init_sys_modes arms).  The
;; arms run only when flow control is *off*, so the policy is (not flow?).
;; Return the leaf status, or #f when there is nothing to do.
(define (unlock-tty-flow fd flow?)
  (if flow?
      #f
      ((force %--tty-flow-unlock) fd)))
