;;; test-m43-imp4.scm --- M43 imp-4: the pure restore and no-echo policy.
;;;
;;; imp-4 moves two policy blocks of src/sysdep.c into (emacs tty-modes):
;;;
;;;   (tty-mode-restore base)      -> a fresh copy of the saved mode
;;;   (tty-mode-no-echo base flags)-> the mode with ICANON and ECHO cleared
;;;
;;; Both are PURE: they run no syscall.  This corpus is the primary proof
;;; of imp-4 (brief.org section 11.1).  It builds the base mode from the
;;; --tty-mode-constants leaf, so the check is portable: an absent name is
;;; absent and the matching rule is skipped.
;;;
;;; The observable restore ("a reset restores the pre-init mode") needs a
;;; pty: this host cannot allocate one (os.openpty gives EACCES, errno
;;; 13), so the .el wrapper reports that case as an environment-gated
;;; INFO skip, not a pass.

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
;; touches low indexes, so a 32-byte vector holds every write.
(define NCCS 32)

(define (flag-mask)
  (let loop ((names '(ICANON ECHO IEXTEN ISIG ICRNL IXON))
             (m 0))
    (if (null? names) m
        (loop (cdr names)
              (if (present? (car names))
                  (logior m (const (car names)))
                  m)))))

;; A base mode with the policy flags set, and a c_cc whose bytes are a
;; known ramp (index + 1), so a copy is observable byte by byte.
(define (base-mode)
  (let ((cc (make-bytevector NCCS 0)))
    (let loop ((i 0))
      (if (< i NCCS)
          (begin (bytevector-u8-set! cc i (modulo (1+ i) 256))
                 (loop (1+ i)))
          cc))
    (list (flag-mask) (flag-mask) (flag-mask) (flag-mask) cc)))

(define (flags-for flow meta)
  (append (list 'flow-control? flow 'meta-key? meta
                'controlling-tty? #t 'quit-char 7)
          consts))

(define (has-bit? word name)
  (and (present? name) (not (zero? (logand word (const name))))))

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

;;; --- tty-mode-restore (brief.org section 5.1) ------------------------

(define restore-base (base-mode))
(define restore-base-cc (list-ref restore-base 4))
(define restore-base-cc-guard (bv-copy restore-base-cc))
(define restored (tty-mode-restore restore-base))

(bool "restore/shape-5-list" (and (list? restored) (= (length restored) 5)))
(bool "restore/c_cc-is-bytevector-32"
      (and (bytevector? (list-ref restored 4))
           (= (bytevector-length (list-ref restored 4)) NCCS)))
;; Every saved field returns unchanged.
(bool "restore/iflag-equal" (= (list-ref restored 0) (list-ref restore-base 0)))
(bool "restore/oflag-equal" (= (list-ref restored 1) (list-ref restore-base 1)))
(bool "restore/cflag-equal" (= (list-ref restored 2) (list-ref restore-base 2)))
(bool "restore/lflag-equal" (= (list-ref restored 3) (list-ref restore-base 3)))
(bool "restore/c_cc-equal" (equal? (list-ref restored 4) restore-base-cc))
;; A *fresh* list and a *fresh* c_cc.
(bool "restore/fresh-list" (not (eq? restored restore-base)))
(bool "restore/fresh-c_cc" (not (eq? (list-ref restored 4) restore-base-cc)))
;; Mutating the result does not touch the caller's base mode.
(bytevector-u8-set! (list-ref restored 4) 0
                    (modulo (1+ (bytevector-u8-ref (list-ref restored 4) 0))
                            256))
(bool "restore/base-c_cc-untouched"
      (equal? (list-ref restore-base 4) restore-base-cc-guard))

;;; --- tty-mode-no-echo (brief.org section 5.2) ------------------------

(define noecho-base (base-mode))
(define noecho-base-cc (bv-copy (list-ref noecho-base 4)))
(define noecho (tty-mode-no-echo noecho-base (flags-for #f #t)))
(define noecho-lflag (list-ref noecho 3))

(bool "noecho/shape-5-list" (and (list? noecho) (= (length noecho) 5)))
(bool "noecho/lflag-ICANON-clear" (not (has-bit? noecho-lflag 'ICANON)))
(bool "noecho/lflag-ECHO-clear" (not (has-bit? noecho-lflag 'ECHO)))
;; Every other lflag bit is kept: only ICANON and ECHO are cleared.
(bool "noecho/lflag-others-kept"
      (= noecho-lflag
         (logand (list-ref noecho-base 3)
                 (lognot (logior (const 'ICANON) (const 'ECHO))))))
(bool "noecho/iflag-kept" (= (list-ref noecho 0) (list-ref noecho-base 0)))
(bool "noecho/oflag-kept" (= (list-ref noecho 1) (list-ref noecho-base 1)))
(bool "noecho/cflag-kept" (= (list-ref noecho 2) (list-ref noecho-base 2)))
;; Every c_cc byte equals the base.
(bool "noecho/c_cc-kept" (equal? (list-ref noecho 4) (list-ref noecho-base 4)))
(bool "noecho/fresh-c_cc" (not (eq? (list-ref noecho 4) (list-ref noecho-base 4))))
;; The base mode stays intact.
(bool "noecho/base-c_cc-untouched"
      (equal? (list-ref noecho-base 4) noecho-base-cc))

;;; --- The rules and the entry points are procedures ------------------

(bool "policy/tty-mode-restore-is-procedure" (procedure? tty-mode-restore))
(bool "policy/tty-mode-no-echo-is-procedure" (procedure? tty-mode-no-echo))
(bool "entry/reset-tty-mode-is-procedure" (procedure? reset-tty-mode))
(bool "entry/suppress-echo-tty-is-procedure" (procedure? suppress-echo-tty))
(bool "entry/unlock-tty-flow-is-procedure" (procedure? unlock-tty-flow))

;;; --- The entry points on a non-tty fd (no pty needed) ---------------
;;;
;;; reset_sys_modes and suppress_echo_on_tty run at the noninteractive
;;; guard under --batch, so the C dispatchers do not run in a gate.
;;; Exercise the entry points directly on fd -1.  Each leaf fails on a
;;; bad fd and returns a negative status; the read fails and returns #f.

(bool "entry/reset-tty-mode-bad-fd-negative-status"
      (let ((r (reset-tty-mode -1 (base-mode))))
        (and (integer? r) (< r 0))))
(bool "entry/reset-tty-mode-nil-base-returns-f"
      (not (reset-tty-mode -1 #f)))
(bool "entry/suppress-echo-tty-bad-fd-returns-f"
      (not (suppress-echo-tty -1)))
(bool "entry/unlock-tty-flow-flow-on-returns-f"
      (not (unlock-tty-flow -1 #t)))
(bool "entry/unlock-tty-flow-flow-off-runs-leaf"
      (let ((r (unlock-tty-flow -1 #f)))
        (and (integer? r) (< r 0))))
