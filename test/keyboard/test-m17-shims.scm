;;; test-m17-shims.scm --- M17 imp-1 test corpus for the C shim DEFUNs in
;;; src/keyboard.c: --recent-keys-index-set!, --total-keys-set!,
;;; --dribble-open-p, --dribble-write-event.
;;;
;;; Sourced by test/keyboard/test-m17-shims.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp.  See docs/m17-plan.org §imp-1 and brief.org.

(use-modules (ice-9 rdelim))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (%sym name)
  (symbol-function name))

(define (no-error? thunk)
  (catch #t
    (lambda () (thunk) #t)
    (lambda (key . args) (list 'error key args))))

;;; --- 0. Registration: all 4 shims resolve ---------------------------
(define shim-names
  '(--recent-keys-index-set! --total-keys-set!
    --dribble-open-p --dribble-write-event))
(for-each
 (lambda (n)
   (check (string-append "registered:" (symbol->string n))
          #t (not (eq? (%sym n) #nil))))
 shim-names)

;;; --- 1. --recent-keys-index-set! / --total-keys-set!: raw int setters
;;; Round-trip: set, read back via the existing getters.  Values are
;;; within the ring's usual range but the setter itself clamps nothing.
((%sym '--recent-keys-index-set!) 3)
(check "recent-keys-index-set!/roundtrip" 3 ((%sym '--recent-keys-index)))
((%sym '--total-keys-set!) 5)
(check "total-keys-set!/roundtrip" 5 ((%sym '--total-keys)))
;; A value at the wrap boundary (lossage_limit - 1) is legal to store.
((%sym '--recent-keys-index-set!) (- ((%sym '--lossage-limit)) 1))
(check "recent-keys-index-set!/boundary"
       (- ((%sym '--lossage-limit)) 1) ((%sym '--recent-keys-index)))
;; Negative input must signal (CHECK_FIXNAT), not silently wrap.
(check "recent-keys-index-set!/negative-signals" #t
       (not (eq? (no-error? (lambda ()
                              ((%sym '--recent-keys-index-set!) -1)))
                 #t)))
(check "total-keys-set!/negative-signals" #t
       (not (eq? (no-error? (lambda () ((%sym '--total-keys-set!) -1)))
                 #t)))
;; Restore sane values so the ring is left coherent for the corpus.
((%sym '--recent-keys-index-set!) 0)
((%sym '--total-keys-set!) 0)

;;; --- 2. --dribble-open-p / --dribble-write-event: raw FILE* write path
;;; In batch no dribble file is open yet, so the getter is nil and the
;;; write shim is a safe no-op (returns nil, no signal).
(check "dribble-open-p/initially-closed" #nil ((%sym '--dribble-open-p)))
(check "dribble-write-event/closed-noop" #nil
       ((%sym '--dribble-write-event) 65))

;; Pick a directory we can actually write to at runtime, so the test
;; still runs in sandboxes that block /tmp.  Prefer $TMPDIR, then /tmp,
;; then the current working directory (test/ under tool/run-tests.sh,
;; the repo root under run-all-tests.el).  Probes each candidate by
;; creating+deleting a file; returns #f if none is writable.
(define (writable-temp-dir)
  (let ((candidates (append (if (getenv "TMPDIR")
                                (list (getenv "TMPDIR"))
                                '())
                            (list "/tmp" (getcwd)))))
    (let loop ((cs candidates))
      (cond
       ((null? cs) #f)
       ((false-if-exception
         (let ((probe (string-append (car cs) "/.m17-write-probe-"
                                     (number->string (getpid)))))
           (call-with-output-file probe (lambda (p) #t))
           (delete-file probe)))
        (car cs))
       (else (loop (cdr cs)))))))

;; Round-trip through a real dribble file: open a temp file, write a
;; mix of events through the shim, close it, then read the bytes back.
;; Expected content mirrors record_char's :4500-4528 tail:
;;   char < 0x100      -> putc(XUFIXNUM)            (65  -> "A")
;;   symbol event      -> '<' + name + '>'          ('foo -> "<foo>")
;;   char >= 0x100     -> " 0x%x"                   (511 -> " 0x1ff")
;; If no writable dir exists, or open-dribble-file itself errors, we
;; report a hard FAIL and continue instead of aborting the whole corpus
;; and silently undercounting (see cr.org Finding 5).
(let* ((dir (writable-temp-dir))
       (path (and dir (string-append dir "/guilemacs-m17-dribble-"
                                     (number->string (getpid))))))
  (if (not path)
      (report "dribble-write-event/roundtrip"
              (list 'FAIL 'no-writable-temp-dir))
      (dynamic-wind
        (lambda () #f)
        (lambda ()
          (let ((open-result
                 (catch #t
                   (lambda () ((%sym 'open-dribble-file) path))
                   (lambda (key . args) (list 'error key args)))))
            (if (not (and (pair? open-result)
                          (eq? (car open-result) 'error)))
                (begin
                  (check "dribble-open-p/open-call-returns-nil" #nil
                         open-result)
                  (check "dribble-open-p/open" #t ((%sym '--dribble-open-p)))
                  ((%sym '--dribble-write-event) 65)
                  ((%sym '--dribble-write-event) 'foo)
                  ((%sym '--dribble-write-event) 511)
                  ((%sym 'open-dribble-file) #nil)
                  (check "dribble-open-p/closed" #nil
                         ((%sym '--dribble-open-p)))
                  (check "dribble-write-event/roundtrip" "A<foo> 0x1ff"
                         (call-with-input-file path read-string)))
                (report "dribble-write-event/roundtrip"
                        (list 'FAIL 'open-error open-result)))))
        (lambda ()
          (false-if-exception ((%sym 'open-dribble-file) #nil))
          (false-if-exception (delete-file path))))))
