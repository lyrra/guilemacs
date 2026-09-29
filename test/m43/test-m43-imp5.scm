;;; test-m43-imp5.scm --- M43 imp-5: the pure tty-size policy.
;;;
;;; imp-5 moves the size policy of get_tty_size and set_window_size of
;;; src/sysdep.c into (emacs tty-modes):
;;;
;;;   (tty-size-wanted probe fallback) -> a (width . height) pair
;;;   (tty-size fd)                    -> the probe applied with no fallback
;;;   (set-tty-size fd height width)   -> the leaf status
;;;
;;; tty-size-wanted is PURE: it runs no syscall.  This corpus is the
;;; primary proof of imp-5 (brief.org section 11.1).  It builds no
;;; platform data, so the check runs on every host.
;;;
;;; The observable size ("a set size reads back") needs a pty: this host
;;; cannot allocate one (os.openpty gives EACCES, errno 13), so the .el
;;; wrapper reports the pty case as an environment-gated INFO skip, not
;;; a pass.

(use-modules (emacs tty-modes))

(define test-results '())
(define (report name status)
  (set! test-results (cons (list name status) test-results)))
(define (bool name value)
  (report name (if value 'PASS 'FAIL)))

;;; --- tty-size-wanted (brief.org section 5) ---------------------------

;; A usable probe wins over the fallback.
(let* ((probe (cons 100 40))
       (fallback (cons 80 24))
       (r (tty-size-wanted probe fallback)))
  (bool "wanted/usable-probe-wins" (equal? r '(100 . 40)))
  (bool "wanted/usable-probe-fresh" (not (eq? r probe))))

;; The result is a fresh pair, so the caller's pair stays intact.
(let* ((probe (cons 100 40))
       (r (tty-size-wanted probe (cons 80 24))))
  (set-car! r 7)
  (bool "wanted/probe-untouched" (= (car probe) 100)))

;; Probe 0 / 0 is not usable, so the fallback wins.
(let ((r (tty-size-wanted (cons 0 0) (cons 80 24))))
  (bool "wanted/probe-zero-zero-uses-fallback" (equal? r '(80 . 24))))

;; A probe with one zero dimension is not usable.
(bool "wanted/probe-zero-width-uses-fallback"
      (equal? (tty-size-wanted (cons 0 24) (cons 80 24)) '(80 . 24)))
(bool "wanted/probe-zero-height-uses-fallback"
      (equal? (tty-size-wanted (cons 80 0) (cons 80 24)) '(80 . 24)))
;; A negative dimension is not usable.
(bool "wanted/probe-negative-uses-fallback"
      (equal? (tty-size-wanted (cons -1 24) (cons 80 24)) '(80 . 24)))

;; A probe of #f is not usable.
(bool "wanted/probe-false-uses-fallback"
      (equal? (tty-size-wanted #f (cons 80 24)) '(80 . 24)))

;; A nil fallback and a bad probe give (0 . 0).
(bool "wanted/false-fallback-and-bad-probe-zero-zero"
      (equal? (tty-size-wanted (cons 0 0) #f) '(0 . 0)))
(bool "wanted/false-fallback-and-false-probe-zero-zero"
      (equal? (tty-size-wanted #f #f) '(0 . 0)))
(bool "wanted/zero-zero-is-fresh"
      (let ((r (tty-size-wanted #f #f)))
        (and (pair? r) (= (car r) 0) (= (cdr r) 0))))

;; The rule is total: every input gives a pair.
(bool "wanted/total-on-junk-inputs"
      (let ((r (tty-size-wanted 'junk 'junk)))
        (and (pair? r) (= (car r) 0) (= (cdr r) 0))))

;; A pair of non-numbers is junk too: the rule must stay total and not
;; raise a type error (cr.org F2).
(bool "wanted/total-on-junk-pair"
      (let ((r (tty-size-wanted '(a . b) '(c . d))))
        (and (pair? r) (= (car r) 0) (= (cdr r) 0))))
;; A bad pair probe still lets a usable fallback win.
(bool "wanted/junk-pair-probe-uses-fallback"
      (equal? (tty-size-wanted '(a . b) (cons 80 24)) '(80 . 24)))

;; A usable fallback is returned fresh too.
(let* ((fallback (cons 80 24))
       (r (tty-size-wanted #f fallback)))
  (bool "wanted/fallback-fresh" (not (eq? r fallback))))

;;; --- The rule and the entry points are procedures --------------------

(bool "policy/tty-size-wanted-is-procedure" (procedure? tty-size-wanted))
(bool "entry/tty-size-is-procedure" (procedure? tty-size))
(bool "entry/set-tty-size-is-procedure" (procedure? set-tty-size))

;;; --- The entry points on a non-tty fd (no pty needed) ----------------
;;;
;;; The C dispatchers get_tty_size_policy / set_window_size_policy run at
;;; the terminal init under a real tty, so they do not run in a gate.
;;; Exercise the entry points directly on fd -1.  The --tty-get-size leaf
;;; fails the ioctl and gives (0 . 0); the --tty-set-size leaf fails and
;;; gives a negative status.

(bool "entry/tty-size-bad-fd-is-zero-zero"
      (equal? (tty-size -1) '(0 . 0)))
(bool "entry/set-tty-size-bad-fd-negative-status"
      (let ((r (set-tty-size -1 24 80)))
        (and (integer? r) (< r 0))))
