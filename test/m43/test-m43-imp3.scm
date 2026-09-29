;;; test-m43-imp3.scm --- M43 imp-3: the pure init_sys_modes mode policy.
;;;
;;; imp-3 moves the terminal-mode flag policy of init_sys_modes
;;; (src/sysdep.c) into (emacs tty-modes).  The pure procedure
;;; tty-mode-wanted takes the base 5-element mode list and the plain flag
;;; list and returns the wanted 5-element mode list.  It runs no syscall.
;;;
;;; This corpus is the primary proof of imp-3 (brief.org section 11).  It
;;; is a table-driven check of the policy against the documented C rule
;;; of brief.org section 5.  It builds the flag values from the
;;; --tty-mode-constants leaf, so the check is portable: an absent name
;;; is absent and the matching rule is skipped.
;;;
;;; The observable tty mode cannot be checked here: this host cannot
;;; allocate a pty (os.openpty gives EACCES, errno 13).  The .el wrapper
;;; reports that pty case as an environment-gated INFO skip, not a pass.

(use-modules (rnrs bytevectors))
(use-modules (emacs tty-modes))

(define test-results '())
(define (report name status)
  (set! test-results (cons (list name status) test-results)))
(define (bool name value)
  (report name (if value 'PASS 'FAIL)))

(define consts (tty-mode-constants))

(define (const name)
  (let loop ((l consts))
    (cond ((null? l) #f)
          ((eq? (car l) name) (cadr l))
          (else (loop (cddr l))))))

(define (present? name)
  (let loop ((l consts))
    (cond ((null? l) #f)
          ((eq? (car l) name) #t)
          (else (loop (cddr l))))))

;; The c_cc array length.  NCCS is 32 on the Linux host; the policy only
;; sets low indexes (VMIN, VTIME, VINTR, VQUIT, VSTART, VSTOP, ...), so
;; a 32-byte vector holds every write.
(define NCCS 32)

(define (flag-mask)
  (let loop ((names '(IGNBRK ICRNL INLCR ISTRIP ECHO ICANON IEXTEN ISIG
                      IXON IXANY ONLCR TAB3 CS8 PARENB))
             (m 0))
    (if (null? names) m
        (loop (cdr names)
              (if (present? (car names))
                  (logior m (const (car names)))
                  m)))))

;; A base mode with every policy flag set, so a clear is observable, and
;; a zeroed c_cc.
(define (base-mode)
  (let ((mask (flag-mask)))
    (list mask mask mask mask (make-bytevector NCCS 0))))

(define (flags-for flow meta ctrl quit)
  (append (list 'flow-control? flow
                'meta-key? meta
                'controlling-tty? ctrl
                'quit-char quit)
          consts))

(define (has-bit? word name)
  (and (present? name) (not (zero? (logand word (const name))))))

(define (cc mode idx) (bytevector-u8-ref (list-ref mode 4) idx))

;; Copy a bytevector.  (bytevector-copy) is unbound in this environment,
;; so copy the bytes directly (the same helper shape as the module).
(define (bv-copy bv)
  (let* ((n (bytevector-length bv))
         (out (make-bytevector n 0)))
    (let loop ((i 0))
      (if (< i n)
          (begin (bytevector-u8-set! out i (bytevector-u8-ref bv i))
                 (loop (1+ i)))
          out))))

;; Build a check name without `format'.  (emacs tty-modes) imports
;; (emacs-elisp runtime), whose `format' is the elisp one, not Scheme's.
(define (b13 bit) (if bit "1" "0"))
(define (tag-of flow meta ctrl)
  (string-append "policy/flow-" (b13 flow)
                 "-meta-" (b13 meta)
                 "-ctrl-" (b13 ctrl)))
(define (ck tag suffix) (string-append tag suffix))

;;; --- The rule of brief.org section 5 ---------------------------------

(define (rule-checks tag flow meta ctrl quit)
  (let* ((b (base-mode))
         (cc-before (list-ref b 4))
         (cc-copy (bv-copy cc-before))
         (m (tty-mode-wanted b (flags-for flow meta ctrl quit)))
         (iflag (list-ref m 0))
         (oflag (list-ref m 1))
         (cflag (list-ref m 2))
         (lflag (list-ref m 3)))
    ;; The result is a plain 5-element list with a bytevector c_cc.
    (bool (ck tag "/shape-5-list") (and (list? m) (= (length m) 5)))
    (bool (ck tag "/c_cc-is-bytevector-32")
          (and (bytevector? (list-ref m 4))
               (= (bytevector-length (list-ref m 4)) NCCS)))
    ;; The policy copies c_cc; it must not mutate the caller's base mode.
    (bool (ck tag "/base-c_cc-untouched")
          (equal? cc-copy cc-before))
    ;; iflag: set IGNBRK; clear ICRNL, INLCR, ISTRIP.
    (bool (ck tag "/iflag-IGNBRK-set") (has-bit? iflag 'IGNBRK))
    (bool (ck tag "/iflag-ICRNL-clear") (not (has-bit? iflag 'ICRNL)))
    (if (present? 'INLCR)
        (bool (ck tag "/iflag-INLCR-clear") (not (has-bit? iflag 'INLCR))))
    (if (present? 'ISTRIP)
        (bool (ck tag "/iflag-ISTRIP-clear") (not (has-bit? iflag 'ISTRIP))))
    ;; lflag: clear ECHO, ICANON, IEXTEN; set ISIG.
    (bool (ck tag "/lflag-ECHO-clear") (not (has-bit? lflag 'ECHO)))
    (bool (ck tag "/lflag-ICANON-clear") (not (has-bit? lflag 'ICANON)))
    (if (present? 'IEXTEN)
        (bool (ck tag "/lflag-IEXTEN-clear") (not (has-bit? lflag 'IEXTEN))))
    (bool (ck tag "/lflag-ISIG-set") (has-bit? lflag 'ISIG))
    ;; flow control: IXON set / IXANY clear when on; else IXON clear.
    (if flow
        (begin
          (bool (ck tag "/iflag-IXON-set") (has-bit? iflag 'IXON))
          (if (present? 'IXANY)
              (bool (ck tag "/iflag-IXANY-clear")
                    (not (has-bit? iflag 'IXANY)))))
        (bool (ck tag "/iflag-IXON-clear") (not (has-bit? iflag 'IXON))))
    ;; oflag: clear ONLCR, TAB3.
    (bool (ck tag "/oflag-ONLCR-clear") (not (has-bit? oflag 'ONLCR)))
    (bool (ck tag "/oflag-TAB3-clear") (not (has-bit? oflag 'TAB3)))
    ;; cflag: with CS8, set CS8 and clear PARENB when meta; else unchanged.
    (if (present? 'CS8)
        (if meta
            (begin
              (bool (ck tag "/cflag-CS8-set") (has-bit? cflag 'CS8))
              (bool (ck tag "/cflag-PARENB-clear")
                    (not (has-bit? cflag 'PARENB))))
            (bool (ck tag "/cflag-unchanged") (= cflag (flag-mask)))))
    ;; c_cc: VMIN = 1, VTIME = 0.
    (bool (ck tag "/c_cc-VMIN-1") (= (cc m (const 'VMIN)) 1))
    (bool (ck tag "/c_cc-VTIME-0") (= (cc m (const 'VTIME)) 0))
    ;; c_cc: VINTR / VQUIT.
    (bool (ck tag "/c_cc-VINTR")
          (= (cc m (const 'VINTR)) (if ctrl quit (const 'CDISABLE))))
    (bool (ck tag "/c_cc-VQUIT")
          (= (cc m (const 'VQUIT)) (if ctrl quit (const 'CDISABLE))))
    ;; c_cc: the shell-layering / editing characters are CDISABLE.
    (for-each
     (lambda (name)
       (if (present? name)
           (bool (ck tag (string-append "/c_cc-" (symbol->string name)
                                        "-CDISABLE"))
                 (= (cc m (const name)) (const 'CDISABLE)))))
     '(VSWTCH VSUSP V_DSUSP VDSUSP VLNEXT VREPRINT VWERASE VDISCARD))
    ;; c_cc: VSTART / VSTOP.
    (if (present? 'VSTART)
        (bool (ck tag "/c_cc-VSTART")
              (= (cc m (const 'VSTART)) (if flow #o21 (const 'CDISABLE)))))
    (if (present? 'VSTOP)
        (bool (ck tag "/c_cc-VSTOP")
              (= (cc m (const 'VSTOP)) (if flow #o23 (const 'CDISABLE)))))))

;; The table: every combination of flow control, meta key, and the
;; controlling tty.  quit_char = 7 (the C-g default, a plain value).
(for-each
 (lambda (combo)
   (rule-checks (tag-of (car combo) (cadr combo) (caddr combo))
                (car combo) (cadr combo) (caddr combo) 7))
 '((#t #t #t) (#t #t #f) (#t #f #t) (#t #f #f)
   (#f #t #t) (#f #t #f) (#f #f #t) (#f #f #f)))

;;; --- The entry point and the constant leaf ---------------------------

(bool "entry/init-tty-mode-is-procedure" (procedure? init-tty-mode))
(bool "policy/tty-mode-wanted-is-procedure" (procedure? tty-mode-wanted))
(bool "consts/is-plain-list" (list? consts))
(bool "consts/IGNBRK-present" (present? 'IGNBRK))
(bool "consts/VMIN-present" (present? 'VMIN))
(bool "consts/CDISABLE-present" (present? 'CDISABLE))

;;; --- The entry point on a non-tty fd (review cr.org F4) --------------
;;;
;;; init_sys_modes returns at the noninteractive guard under --batch, so
;;; the C dispatcher and the Scheme entry point run in no gate.  Exercise
;;; the entry point directly on fd -1: it computes the wanted mode and
;;; applies it with the imp-2 leaf, which fails on a bad fd and returns a
;;; negative status.  This runs on every host (no pty needed).

(define (plain-flags flow meta ctrl quit)
  (list 'flow-control? flow 'meta-key? meta 'controlling-tty? ctrl
        'quit-char quit))

(bool "entry/init-tty-mode-fd-minus-one-returns-wanted"
      (let* ((b (base-mode))
             (fp (plain-flags #f #t #t 7))
             (w (init-tty-mode -1 b fp)))
        (equal? w (tty-mode-wanted b (append fp consts)))))

(bool "entry/tty-set-mode-bad-fd-negative-status"
      (let ((r (tty-set-mode -1 (base-mode) #f)))
        (and (integer? r) (< r 0))))
