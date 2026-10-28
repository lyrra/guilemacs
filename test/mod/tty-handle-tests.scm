;;; SRFI-64 tests for the M61 per-TTY handle of (emacs tty-output):
;;; imp-1 (the value, the write) and imp-2 (the flush, the termscript copy).

;; COVER: the handle value, its 5 states, the closed-use error, the
;; after-write verdict, and the retry loop, all of mod/emacs/tty-output.scm.
;; Plain `guile -L mod` loads the module with no Emacs binary.

;; LIMIT: read this before you trust a green run.
;;   1. This suite proves the PURE Scheme part of the handle only.
;;   2. It starts no Emacs and runs no C build, so it proves NO C seam.
;;      The C identity table, the leaf --tty-handle-write, the bootstrap
;;      --tty-handle, and the routed normal write are proved by the
;;      m61-imp1 PTY group of test/pty-driver.py, not here.  The 2
;;      imp-2 leaves (--tty-handle-flush, --tty-handle-termscript) and
;;      the 0 answer of a tty with no termscript stream are proved by the
;;      m61-imp2 PTY group, not here: a plain Guile session has no tty.
;;   3. It mutates NO module binding.  A `module-set!' of a leaf inside a
;;      declarative module is inlined by the compiler, so a stub test
;;      silently stops testing anything once a compiled .go cache exists.
;;      The retry loop therefore takes its write procedure as an
;;      ARGUMENT (tty-handle-write-all-with), and the test passes a plain
;;      lambda.
;;   4. A rename of an export breaks this suite.  A broken C leaf leaves
;;      it green.

(use-modules (srfi srfi-64)
             (rnrs bytevectors)      ; bytevector-length in this module
             (emacs tty-output))

;; Pinned case count.  A suite that loses a case must fail: each suite
;; pins its own count (docs/kb.org test-mod-standalone-suite).
;; The pin counts EVERY pass, the Z1 check below included.  That is the
;; shape of the 4 sibling suites of this directory: their exit block is
;; (= passes expected-passes) (cr.org F2).  imp-1 carried 31; imp-2 adds
;; the 12 G checks, the 4 H checks and Z1, so 48.
(define expected-passes 48)

;; No SRFI-64 log file: it would land in the working directory.  See the
;; same note, docs/kb.org test-mod-standalone-suite.
(set! test-log-to-file #f)

(test-begin "Guilemacs tty-handle module")
(define test-runner (test-runner-current))

;; --- A. the value shape ---------------------------------------------

(define h (make-tty-handle 7 'borrowed))

(test-equal "A1 the tagged value is a tty handle" #t (tty-handle? h))
(test-equal "A2 the identity is a plain fixnum" 7 (tty-handle-id h))
(test-equal "A3 the state is a plain symbol" 'borrowed (tty-handle-state h))

;; A foreign value that LOOKS like a box must not be a handle.  The tag
;; and the length are both required.
(test-equal "A4 the tag symbol alone is not a handle"
            #f (tty-handle? 'tty-handle))
(test-equal "A5 a 4-slot vector of the same tag is not a handle"
            #f (tty-handle? (vector 'tty-handle 7 'borrowed 'extra)))
(test-equal "A6 a plain number is not a handle" #f (tty-handle? 7))

;; --- B. the 5 states ------------------------------------------------

(test-equal "B1 the 5 states, in the documented order"
            '(borrowed owned transferred duplicated closed)
            tty-handle-states)

(test-equal "B2 every state but closed is open"
            '(#t #t #t #t #f)
            (map (lambda (s) (tty-handle-open? (make-tty-handle 1 s)))
                 tty-handle-states))

;; A state change builds a NEW value: the old value keeps its state, so
;; the module needs no module-level mutable state.
(define owned (tty-handle-with-state h 'owned))
(test-equal "B3 the new value holds the new state"
            'owned (tty-handle-state owned))
(test-equal "B4 the old value keeps its state" 'borrowed (tty-handle-state h))
(test-equal "B5 the new value keeps the identity" 7 (tty-handle-id owned))

(define closed (tty-handle-close owned))
(test-equal "B6 close gives the state closed" 'closed (tty-handle-state closed))
(test-equal "B7 a closed handle is not open" #f (tty-handle-open? closed))
(test-equal "B8 close keeps the identity" 7 (tty-handle-id closed))

;; --- C. the closed-use error ----------------------------------------

;; An open handle is returned as-is.
(test-equal "C1 an open handle checks clean" h (tty-handle-check-open h))

;; A closed handle raises a plain Scheme error BEFORE any C call.
(test-equal "C2 a closed handle raises" #t
            (catch #t
                   (lambda () (tty-handle-check-open closed) #f)
                   (lambda (key . args) #t)))

;; A value that is not a handle raises the same way.
(test-equal "C3 a non-handle raises" #t
            (catch #t
                   (lambda () (tty-handle-check-open 7) #f)
                   (lambda (key . args) #t)))

;; The ONE write operation checks the state first, so a closed handle
;; never reaches the C leaf.
(test-equal "C4 a closed handle write raises" #t
            (catch #t
                   (lambda () (tty-handle-write closed #vu8(65)) #f)
                   (lambda (key . args) #t)))

;; --- D. the after-write verdict -------------------------------------

(test-equal "D1 a full write is done" "done"
            (tty-handle-write-verdict 3 3))
(test-equal "D2 a short write with no error is retried" "retry"
            (tty-handle-write-verdict 1 3))
(test-equal "D3 a negative leaf answer is a give-up" "give-up"
            (tty-handle-write-verdict -9 3))

;; --- E. the retry loop ----------------------------------------------

;; A full write is one call of the write procedure.
(define calls 0)
(define (full h bytes) (set! calls (+ calls 1)) (bytevector-length bytes))
(test-equal "E1 a full write reports the full count"
            6 (tty-handle-write-all-with full h #vu8(1 2 3 4 5 6)))
(test-equal "E2 a full write calls the write procedure once" 1 calls)

;; A short write is retried until the count is complete.  The procedure
;; answers 2 on every call and reads no byte, so this proves the CALL
;; COUNT and the SUM only: byte order and byte content are proved by the
;; m61-imp1 PTY group, not here.
(set! calls 0)
(define (short h bytes)
  (set! calls (+ calls 1))
  (min 2 (bytevector-length bytes)))
(test-equal "E3 a short write is retried to completion"
            6 (tty-handle-write-all-with short h #vu8(1 2 3 4 5 6)))
(test-equal "E4 the retry loop made 3 calls" 3 calls)

;; No progress does not spin: the loop reports what went out.
(set! calls 0)
(define (stuck h bytes) (set! calls (+ calls 1)) 0)
(test-equal "E5 no progress reports 0 and stops"
            0 (tty-handle-write-all-with stuck h #vu8(1 2 3)))
(test-equal "E6 no progress made one call" 1 calls)

;; A hard failure returns the negated errno unchanged.
(define (hard h bytes) -32)
(test-equal "E7 a hard failure returns the negated errno"
            -32 (tty-handle-write-all-with hard h #vu8(1 2 3)))

;; An empty bytevector needs no call and reports 0.
(test-equal "E8 an empty write reports 0"
            0 (tty-handle-write-all-with full h #vu8()))

;; --- F. the C-facing form of the retry loop ------------------------
;;
;; The routed normal write in src/term.c passes a plain identity and a
;; plain bytevector to tty-handle-write-all-borrowed (docs/m61-plan.org
;; section 3.1.3; the review of 9c2d457f2, findings F10 and F11).
;; The two guards below are pure: they answer -EBADF before any C call,
;; so this suite proves them with no Emacs binary.
;;
;; The literal -9 is -EBADF on Linux only.  It stays here because the
;; leaf --tty-handle-write answers (- errno EBADF) for an unknown
;; identity and src/term.c holds the same -EBADF.  A host with a
;; different EBADF must change both sites.

(test-equal "F1 a negative identity is -EBADF"
            -9 (tty-handle-write-all-borrowed -1 #vu8(65)))
(test-equal "F2 a non-integer identity is -EBADF"
            -9 (tty-handle-write-all-borrowed 'seven #vu8(65)))

;; --- G. the 2 operations of imp-2 -----------------------------------
;;
;; The 4 new exports: the 2 operations and their C-facing forms.  Each
;; name below is the imported binding, so a name that the module does not
;; export stops this file.

(test-equal "G1 the flush operation is exported"
            #t (procedure? tty-handle-flush))
(test-equal "G2 the termscript copy is exported"
            #t (procedure? tty-handle-termscript))
(test-equal "G3 the C-facing flush is exported"
            #t (procedure? tty-handle-flush-borrowed))
(test-equal "G4 the C-facing termscript copy is exported"
            #t (procedure? tty-handle-termscript-borrowed))

;; The 2 new leaves are DELAYED references of the module, so a name that
;; the C side does not define fails in the PTY group and not here
;; (LIMIT 2).  The state check runs BEFORE the leaf in both operations,
;; so a closed handle raises with no C call and no Emacs binary.
(test-equal "G5 a closed handle flush raises" #t
            (catch #t
                   (lambda () (tty-handle-flush closed) #f)
                   (lambda (key . args) #t)))
(test-equal "G6 a closed handle termscript copy raises" #t
            (catch #t
                   (lambda () (tty-handle-termscript closed #vu8(65)) #f)
                   (lambda (key . args) #t)))

;; A value that is not a handle raises the same way.
(test-equal "G7 a non-handle flush raises" #t
            (catch #t
                   (lambda () (tty-handle-flush 7) #f)
                   (lambda (key . args) #t)))
(test-equal "G8 a non-handle termscript copy raises" #t
            (catch #t
                   (lambda () (tty-handle-termscript 'h #vu8(65)) #f)
                   (lambda (key . args) #t)))

;; The C-facing forms answer -EBADF, with no C call, for an identity that
;; no table entry can hold.  These are the same 2 guards as F1 and F2.
(test-equal "G9 a negative identity is -EBADF for the flush"
            -9 (tty-handle-flush-borrowed -1))
(test-equal "G10 a non-integer identity is -EBADF for the flush"
            -9 (tty-handle-flush-borrowed 'seven))
(test-equal "G11 a negative identity is -EBADF for the termscript copy"
            -9 (tty-handle-termscript-borrowed -1 #vu8(65)))
(test-equal "G12 a non-integer identity is -EBADF for the termscript copy"
            -9 (tty-handle-termscript-borrowed 'seven #vu8(65)))

;; --- H. the plain triple that the M54 verdict site feeds --------------
;;
;; m54_tty_termscript_verdict passes (copied, len, err) as 3 PLAIN values
;; and reads no global errno (cr.org F3).  The C sites that build the
;; triple are proved by the m61-imp2 and the m54-imp3 PTY groups; this
;; section proves the Scheme decision that consumes it.  The literal 13
;; is EACCES on Linux, a real error and neither EINTR nor EAGAIN.
(test-equal "H1 a full copy is done"
            "done" (tty-write-verdict 10 10 0))
(test-equal "H2 a short copy with no errno retries"
            "retry" (tty-write-verdict 5 10 0))
(test-equal "H3 a short copy with a real errno gives up"
            "give-up" (tty-write-verdict 5 10 13))
(test-equal "H4 a copy of 0 bytes of 0 is done"
            "done" (tty-write-verdict 0 0 0))

;; --- the pinned count ----------------------------------------------

;; 1 pass is still to come when this line runs: the pass of this check.
;; So the count here is the pin minus 1, and the exit block below compares
;; the full pin (cr.org F2).
(test-assert "Z1 every case ran"
             (= expected-passes (1+ (test-runner-pass-count test-runner))))

;; The summary line and the explicit exit.  The SRFI-64 default exit status
;; is 0 even with an unexpected failure, so a runner that reads the status
;; only would report a green gate for a red suite.  Same shape as the 4
;; sibling suites of this directory: the pin counts every pass, so the
;; compare is (= passes expected-passes) (cr.org F2).
(let ((passes (test-runner-pass-count test-runner))
      (fails  (test-runner-fail-count test-runner)))
  (format #t "~a: ~a passed, ~a failed (expected ~a passed)~%"
          "Guilemacs tty-handle module" passes fails expected-passes)
  (exit (if (and (zero? fails) (= passes expected-passes)) 0 1)))

(test-end "Guilemacs tty-handle module")
