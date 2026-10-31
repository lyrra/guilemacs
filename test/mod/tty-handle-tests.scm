;;; SRFI-64 tests for the M61 per-TTY handle of (emacs tty-output):
;;; imp-1 (the value, the write) and imp-2 (the flush, the termscript copy),
;;; repaired by imp-2b (the carrier of a count and an error).

;; COVER: the handle value, its 5 states, the closed-use error, the
;; after-write verdict, the retry loop and the carrier, all of
;; mod/emacs/tty-output.scm.  Plain `guile -L mod` loads the module with no
;; Emacs binary.

;; LIMIT: read this before you trust a green run.
;;   1. This suite proves the PURE Scheme part of the handle only.
;;   2. It starts no Emacs and runs no C build, so it proves NO C seam.
;;      The C identity table, the leaf --tty-handle-write, the bootstrap
;;      --tty-handle, and the routed normal write are proved by the
;;      m61-imp1 PTY group of test/pty-driver.py, not here.  The 2
;;      imp-2 leaves (--tty-handle-flush, --tty-handle-termscript) and
;;      the 0 answer of a tty with no termscript stream are proved by the
;;      m61-imp2 PTY group, not here: a plain Guile session has no tty.
;;   3. The raise cases of section I run the SCHEME retry loop only, with
;;      an injected write procedure.  The rule "a #f answer writes no
;;      byte" of src/term.c is proved end to end by the m61-imp2g PTY
;;      case `raise-e2e`, which injects a raise into the real C dispatch
;;      (a `module-set!' of the binding that the C hub reads), not here.
;;      The 6 K checks of section K prove the POLICY procedure of that
;;      seam; the C side of it is proved by `clean-run-e2e` and
;;      `raise-e2e`.
;;   4. It mutates NO module binding.  A `module-set!' of a leaf inside a
;;      declarative module is inlined by the compiler, so a stub test
;;      silently stops testing anything once a compiled .go cache exists.
;;      The retry loop therefore takes its write procedure as an
;;      ARGUMENT (tty-handle-write-all-with), and the test passes a plain
;;      lambda.
;;   5. A rename of an export breaks this suite.  A broken C leaf leaves
;;      it green.

(use-modules (srfi srfi-64)
             (srfi srfi-13)          ; string-contains in the raise checks
             (rnrs bytevectors)      ; bytevector-length in this module
             (emacs tty-output))

;; Pinned case count.  A suite that loses a case must fail: each suite
;; pins its own count (docs/kb.org test-mod-standalone-suite).
;; The pin counts EVERY pass, the Z1 check below included.  That is the
;; shape of the 4 sibling suites of this directory: their exit block is
;; (= passes expected-passes).  imp-1 carried 31; imp-2 added the 12 G
;; checks, the 4 H checks and Z1, so 48; imp-2b adds the C5 to C7 checks,
;; the H5 to H7 checks, the F3 EBADF pin, the 5 I checks and Z1, so 65;
;; imp-2g adds D4, J1 and J2, so 68 (MEASURED 2026-10-31 with
;; ./test/mod/run-mod-tests.sh); imp-2g adds the 6 K checks, so 74; the
;; repair of review cr.org C3 adds K7, so 75; the repair of review cr.org
;; CR2 adds G13 to G15, so 78.
(define expected-passes 78)

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
;;
;; The raise shape, MEASURED on this host in plain Guile:
;;
;;   (misc-error #f "tty-handle: the identity is closed ~S" (7) #f)
;;   (misc-error #f "tty-handle: not a tty handle ~S" (7) #f)
;;
;; MEASURED too: the message field can carry the 2-field form "~A ~S"
;; with the text and the irritants inside one list, because the module
;; builds this error through (emacs-elisp runtime).  The assertion below
;; accepts BOTH shapes; it pins the key, the diagnostic text and the
;; irritants, and it rejects any other key.
;;
;; A call that reaches an unavailable C leaf raises a DIFFERENT condition:
;;
;;   (wrong-type-arg #f "Wrong type to apply: ~S" (#nil) (#nil))
;;
;; A check that catches every key accepts both, so it stays green when the
;; closed-state guard is removed (milestone.org =findings= F4).

;; Answer the pair (key . args) of the raise of THUNK, or 'no-raise.
(define (raised-answer thunk)
  (catch #t
    (lambda () (thunk) 'no-raise)
    (lambda (key . args) (cons key args))))

;; True when ANSWER is the plain Scheme error of TEXT raised with
;; IRRITANTS.  The KEY must be misc-error, and the printed arguments must
;; hold the diagnostic TEXT and every IRRITANT.  A caller that renames the
;; text, drops the irritant or raises another key fails here; a
;; wrong-type-arg from the C boundary fails on the key alone.
(define (misc-error-with? answer text irritants)
  (define (holds-all? printed items)
    (or (null? items)
        (and (string-contains printed (format #f "~a" (car items)))
             (holds-all? printed (cdr items)))))
  (and (pair? answer)
       (eq? 'misc-error (car answer))
       (let ((printed (format #f "~a" (cdr answer))))
         (and (string-contains printed text)
              (holds-all? printed irritants)))))

;; An open handle is returned as-is.
(test-equal "C1 an open handle checks clean" h (tty-handle-check-open h))

;; A closed handle raises the closed-identity error BEFORE any C call.
(test-equal "C2 a closed handle raises the closed-identity error" #t
            (misc-error-with? (raised-answer
                               (lambda () (tty-handle-check-open closed)))
                              "tty-handle: the identity is closed" '(7)))

;; A value that is not a handle raises the not-a-handle error.
(test-equal "C3 a non-handle raises the not-a-handle error" #t
            (misc-error-with? (raised-answer
                               (lambda () (tty-handle-check-open 7)))
                              "tty-handle: not a tty handle" '(7)))

;; The ONE write operation checks the state first, so a closed handle
;; never reaches the C leaf.  The exact condition proves it: a reached C
;; leaf would raise wrong-type-arg on this host (LIMIT 2).
(test-equal "C4 a closed handle write raises the closed-identity error" #t
            (misc-error-with? (raised-answer
                               (lambda () (tty-handle-write closed #vu8(65))))
                              "tty-handle: the identity is closed" '(7)))

;; The assertion itself must REJECT the C-boundary condition, else C4 could
;; stay green with the guard gone.  This check feeds the measured
;; wrong-type-arg shape to the same predicate.
(test-equal "C5 the assertion rejects a C-boundary error" #f
            (misc-error-with?
             (cons 'wrong-type-arg (list #f "Wrong type to apply: ~S"
                                        '(#nil) #f))
             "tty-handle: the identity is closed" '(7)))
;; The positive control of the assertion itself: the MEASURED
;; closed-identity answer passes it, so C4 can not pass by accident.
(test-equal "C7 the assertion accepts the measured closed-identity answer" #t
            (misc-error-with?
             (cons 'misc-error
                   (list #f "tty-handle: the identity is closed ~S" '(7) #f))
             "tty-handle: the identity is closed" '(7)))

;; The positive control: an OPEN handle does reach the unavailable C leaf,
;; and its error is NOT the closed-identity error.  Together with C4 this
;; proves that the 2 conditions are distinguishable on this host.
(test-equal "C6 an open handle reaches the C leaf and raises a C error" #t
            (let ((answer (raised-answer
                           (lambda () (tty-handle-write h #vu8(65))))))
              (and (pair? answer) (eq? 'wrong-type-arg (car answer)))))

;; --- D. the after-write verdict -------------------------------------
;;
;; Since imp-2g the verdict takes the carrier #(count errno) of ONE call,
;; not a plain fixnum (milestone.org =findings= F6).

(test-equal "D1 a full write is done" "done"
            (tty-handle-write-verdict (vector 3 0) 3))
(test-equal "D2 a short write with no error is retried" "retry"
            (tty-handle-write-verdict (vector 1 0) 3))
(test-equal "D3 a carrier with an errno is a give-up" "give-up"
            (tty-handle-write-verdict (vector 0 9) 3))

;; The verdict reads the errno and not the count: a carrier that moved
;; EVERY byte and still holds an errno is a give-up too.
(test-equal "D4 a full count with an errno is still a give-up" "give-up"
            (tty-handle-write-verdict (vector 3 28) 3))

;; --- E. the retry loop and its carrier ------------------------------
;;
;; Every answer of the loop is the plain carrier #(count errno), read
;; through the exported accessors.  A count and an error travel together,
;; so a caller never infers zero progress from an error (milestone.org
;; =findings= F3).
;;
;; Since imp-2g each write procedure answers the carrier of ONE call, so a
;; test lambda that answers a plain fixnum would stop the loop.

;; A full write is one call of the write procedure.
(define calls 0)
(define (full h bytes)
  (set! calls (+ calls 1))
  (tty-handle-outcome (bytevector-length bytes) 0))
(define (carrier-count answer) (tty-handle-outcome-count answer))
(define (carrier-errno answer) (tty-handle-outcome-errno answer))

(test-equal "E1 a full write reports the full count"
            6 (carrier-count (tty-handle-write-all-with full h #vu8(1 2 3 4 5 6))))
(test-equal "E2 a full write calls the write procedure once" 1 calls)

;; A short write is retried until the count is complete.  The procedure
;; answers 2 on every call and reads no byte, so this proves the CALL
;; COUNT and the SUM only: byte order and byte content are proved by the
;; m61-imp1 PTY group, not here.
(set! calls 0)
(define (short h bytes)
  (set! calls (+ calls 1))
  (tty-handle-outcome (min 2 (bytevector-length bytes)) 0))
(test-equal "E3 a short write is retried to completion"
            6 (carrier-count (tty-handle-write-all-with short h
                                                        #vu8(1 2 3 4 5 6))))
(test-equal "E4 the retry loop made 3 calls" 3 calls)

;; No progress does not spin: the loop reports what went out.
(set! calls 0)
(define (stuck h bytes) (set! calls (+ calls 1)) (tty-handle-outcome 0 0))
(test-equal "E5 no progress reports 0 and stops"
            0 (carrier-count (tty-handle-write-all-with stuck h #vu8(1 2 3))))
(test-equal "E6 no progress made one call" 1 calls)

;; A hard failure carries its positive errno with the count.
(define (hard h bytes) (tty-handle-outcome 0 32))
(test-equal "E7 a hard failure reports the errno"
            32 (carrier-errno (tty-handle-write-all-with hard h #vu8(1 2 3))))

;; An empty bytevector needs no call and reports 0.
(test-equal "E8 an empty write reports 0 and no error"
            (vector 0 0) (tty-handle-write-all-with full h #vu8()))

;; --- F. the C-facing form of the retry loop ------------------------
;;
;; The routed normal write in src/term.c passes a plain identity and a
;; plain bytevector to tty-handle-write-all-borrowed (docs/m61-plan.org
;; section 3.1.3).  The two guards below are pure: they answer the carrier
;; #(0 9) before any C call, so this suite proves them with no Emacs
;; binary.
;;
;; The ONE Scheme site of the positive EBADF is the definition
;; `tty-handle-ebadf` (mod/emacs/tty-output.scm), and src/term.c names
;; that definition in its own comment.  The cases below read the
;; definition, never a literal.

(test-equal "F1 a negative identity is EBADF with count 0"
            (vector 0 tty-handle-ebadf)
            (tty-handle-write-all-borrowed -1 #vu8(65)))
(test-equal "F2 a non-integer identity is EBADF with count 0"
            (vector 0 tty-handle-ebadf)
            (tty-handle-write-all-borrowed 'seven #vu8(65)))

;; F3.  The value of that one site.  9 is the Linux EBADF, so this is a
;; HOST DEPENDENCY, not a portable constant: a host with a different
;; EBADF must change the Scheme definition and the C macro TOGETHER, and
;; then this case.  The case exists so that a silent change of the
;; Scheme value can not happen.
(test-equal "F3 the Scheme EBADF value is the pinned host value"
            9 tty-handle-ebadf)

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
;; (LIMIT 2).  The state check runs BEFORE the leaf in both operations, so
;; a closed handle raises the closed-identity error with no C call.
(test-equal "G5 a closed handle flush raises the closed-identity error" #t
            (misc-error-with? (raised-answer
                               (lambda () (tty-handle-flush closed)))
                              "tty-handle: the identity is closed" '(7)))
(test-equal "G6 a closed handle termscript copy raises the closed-identity error"
            #t
            (misc-error-with?
             (raised-answer (lambda () (tty-handle-termscript closed #vu8(65))))
             "tty-handle: the identity is closed" '(7)))

;; A value that is not a handle raises the not-a-handle error.
(test-equal "G7 a non-handle flush raises the not-a-handle error" #t
            (misc-error-with? (raised-answer (lambda () (tty-handle-flush 7)))
                              "tty-handle: not a tty handle" '(7)))
(test-equal "G8 a non-handle termscript copy raises the not-a-handle error" #t
            (misc-error-with?
             (raised-answer (lambda () (tty-handle-termscript 'h #vu8(65))))
             "tty-handle: not a tty handle" '(h)))

;; The C-facing forms answer the carrier EBADF, with no C call, for an
;; identity that no table entry can hold.  The value is read from the ONE
;; Scheme definition tty-handle-ebadf, never from a literal.
(test-equal "G9 a negative identity is -EBADF for the flush"
            (- tty-handle-ebadf) (tty-handle-flush-borrowed -1))
(test-equal "G10 a non-integer identity is -EBADF for the flush"
            (- tty-handle-ebadf) (tty-handle-flush-borrowed 'seven))
(test-equal "G11 a negative identity is EBADF with count 0 for the copy"
            (vector 0 tty-handle-ebadf)
            (tty-handle-termscript-borrowed -1 #vu8(65)))
(test-equal "G12 a non-integer identity is EBADF with count 0 for the copy"
            (vector 0 tty-handle-ebadf)
            (tty-handle-termscript-borrowed 'seven #vu8(65)))

;; The identity test of the 3 C-facing forms is POSITIVE, because
;; src/term.c never gives an identity below 1 (m61_tty_handle_next starts
;; at 1).  An identity of 0 is therefore NOT a handle: it must answer
;; EBADF and it must not reach a leaf, where the raise of an unknown
;; handle would be reported as UNKNOWN progress (review cr.org CR2).
(test-equal "G13 identity 0 is EBADF with count 0 for the copy"
            (vector 0 tty-handle-ebadf)
            (tty-handle-termscript-borrowed 0 #vu8(65)))
(test-equal "G14 identity 0 is -EBADF for the flush"
            (- tty-handle-ebadf) (tty-handle-flush-borrowed 0))
(test-equal "G15 identity 0 is EBADF with count 0 for the write"
            (vector 0 tty-handle-ebadf)
            (tty-handle-write-all-borrowed 0 #vu8(65)))

;; --- H. the count and the errno of the copy -------------------------
;;
;; m54_tty_termscript_verdict passes (copied, len, err) as 3 PLAIN values
;; and reads no global errno.  The C sites that build the triple are
;; proved by the m61-imp2 PTY group; this section proves the Scheme
;; decision and the record that consume it.  The literal 13 is EACCES on
;; Linux, a real error and neither EINTR nor EAGAIN.
(test-equal "H1 a full copy is done"
            "done" (tty-write-verdict 10 10 0))
(test-equal "H2 a short copy with no errno retries"
            "retry" (tty-write-verdict 5 10 0))
(test-equal "H3 a short copy with a real errno gives up"
            "give-up" (tty-write-verdict 5 10 13))
(test-equal "H4 a copy of 0 bytes of 0 is done"
            "done" (tty-write-verdict 0 0 0))

;; The record that C builds from a copy answer keeps the MEASURED count
;; when the copy fails (milestone.org =findings= F3): 5 bytes that moved
;; and then failed record 5, not 0.
(test-equal "H5 a partial copy that failed records its 5 bytes"
            (list 5 1 1)
            (let ((r (tty-termscript-copy-handle 5 10 28)))
              (list (tty-out-handle-bytes r)
                    (tty-out-handle-short-writes r)
                    (tty-out-handle-hard-errors r))))
(test-equal "H6 a partial copy with no errno records a retry"
            (list 5 1 0)
            (let ((r (tty-termscript-copy-handle 5 10 0)))
              (list (tty-out-handle-bytes r)
                    (tty-out-handle-short-writes r)
                    (tty-out-handle-hard-errors r))))
(test-equal "H7 a complete copy records every byte"
            (list 10 0 0)
            (let ((r (tty-termscript-copy-handle 10 10 0)))
              (list (tty-out-handle-bytes r)
                    (tty-out-handle-short-writes r)
                    (tty-out-handle-hard-errors r))))

;; --- I. a raise, and the carrier that replaces a replay -------------
;;
;; The F1 case of milestone.org =findings=: a raise can stop the retry
;; loop after a prefix of the bytes is on the stream.  The 3 cases of
;; brief.org section 3.4 are: a raise before the first byte, a raise after
;; a partial write, and a raise after a completed write.  SINK is the
;; stream: it collects every byte that the write procedure hands out, so a
;; byte that travels twice is visible.
;;
;; LIMIT 3: this fixture runs the SCHEME loop only.  It proves that the
;; loop does NOT catch and does NOT retry a raise, and that each prefix
;; travels ONE time.  The rule "the C caller must not write on #f" lives
;; in src/term.c and is not reached here.
(define sink '())
(define (sink-reset!) (set! sink '()))
(define (sink-write! slice)
  (let ((n (bytevector-length slice)))
    (let loop ((i 0))
      (if (< i n)
          (begin (set! sink (cons (bytevector-u8-ref slice i) sink))
                 (loop (+ i 1)))))))
(define (sink-bytes) (reverse sink))

;; The first N bytes of BV as a new bytevector.
(define (first-bytes bv n)
  (let ((out (make-bytevector n 0)))
    (bytevector-copy! bv 0 out 0 n)
    out))

;; 1. A raise before the first byte: no byte reaches the stream.
(sink-reset!)
(define (raise-at-once h bytes) (raise 'boom))
(test-equal "I1 a raise before the first byte leaves the loop" 'no-answer
            (let ((answer (raised-answer
                           (lambda ()
                             (tty-handle-write-all-with raise-at-once h
                                                        #vu8(1 2 3))))))
              (if (eq? 'no-raise answer) 'no-raise 'no-answer)))
(test-equal "I2 the raise before the first byte wrote no byte" '()
            (sink-bytes))

;; 2. A raise after a partial write: the prefix is on the stream ONE time
;; and the loop does not write it again.
(sink-reset!)
(set! calls 0)
(define (partial-then-raise h bytes)
  (set! calls (+ calls 1))
  (if (= calls 1)
      (let ((n (min 2 (bytevector-length bytes))))
        (sink-write! (first-bytes bytes n))
        (tty-handle-outcome n 0))
      (raise 'boom)))
(test-equal "I3 a raise after a partial write leaves the loop" 'no-answer
            (let ((answer (raised-answer
                           (lambda ()
                             (tty-handle-write-all-with
                              partial-then-raise h #vu8(1 2 3 4 5 6))))))
              (if (eq? 'no-raise answer) 'no-raise 'no-answer)))
(test-equal "I4 the partial prefix is on the stream one time" '(1 2)
            (sink-bytes))

;; 3. A raise after a completed write: the whole payload is on the stream
;; ONE time.
(sink-reset!)
(define (write-then-raise h bytes)
  (sink-write! bytes)
  (raise 'boom))
(test-equal "I5 a raise after a completed write leaves the loop" 'no-answer
            (let ((answer (raised-answer
                           (lambda ()
                             (tty-handle-write-all-with
                              write-then-raise h #vu8(1 2 3 4 5 6))))))
              (if (eq? 'no-raise answer) 'no-raise 'no-answer)))
(test-equal "I6 the completed payload is on the stream one time"
            '(1 2 3 4 5 6) (sink-bytes))

;; 4. The C-facing wrapper answers #f, the ONE "progress unknown" answer,
;; when the leaf raises.  There is no C leaf in a plain Guile session, so
;; this call reaches the raise path (LIMIT 2).
(test-equal "I7 the write wrapper answers #f when the progress is unknown"
            #f (tty-handle-write-all-borrowed 7 #vu8(65)))
(test-equal "I8 the copy wrapper answers #f when the progress is unknown"
            #f (tty-handle-termscript-borrowed 7 #vu8(65)))

;; 5. A hard failure AFTER a partial write carries BOTH values: this is
;; the F3 defect that a plain count can not express.
(define (partial-then-hard h bytes)
  (if (= 0 (bytevector-length bytes))
      (tty-handle-outcome 0 0)
      (tty-handle-outcome 0 32)))
(set! calls 0)
(define (two-then-hard h bytes)
  (set! calls (+ calls 1))
  (if (= calls 1)
      (tty-handle-outcome (min 2 (bytevector-length bytes)) 0)
      (tty-handle-outcome 0 32)))
(test-equal "I9 a hard failure after a partial write keeps both values"
            (vector 2 32)
            (tty-handle-write-all-with two-then-hard h #vu8(1 2 3 4 5 6)))
(set! calls 0)
(test-equal "I10 the carrier accessors agree with the plain vector"
            (list 2 32)
            (let ((answer (tty-handle-write-all-with two-then-hard h
                                                     #vu8(1 2 3 4 5 6))))
              (list (carrier-count answer) (carrier-errno answer))))

;; --- J. the count of the FAILING call (imp-2g, F6) ------------------
;;
;; The 2 cases below are the defect of milestone.org =findings= F6 in its
;; smallest form: 1 call moves a nonzero prefix AND then fails, so the loop
;; must add the count of THAT call to its total.  A loop that keeps only
;; the total of the earlier calls answers fewer bytes than reached the
;; stream.

;; J1: ONE call answers #(5 ENOSPC) for a 12-byte payload.
(define (five-then-fail h bytes) (tty-handle-outcome 5 28))
(test-equal "J1 one failing call keeps its own 5 bytes"
            (vector 5 28)
            (tty-handle-write-all-with five-then-fail h
                                       #vu8(1 2 3 4 5 6 7 8 9 10 11 12)))

;; J2: the first call answers #(2 0) and the second #(3 ENOSPC).  A loop
;; that keeps only TOTAL answers 2 and loses the 3 of the failing call.
(set! calls 0)
(define (two-then-three-then-fail h bytes)
  (set! calls (+ calls 1))
  (if (= calls 1)
      (tty-handle-outcome 2 0)
      (tty-handle-outcome 3 28)))
(test-equal "J2 the failing second call adds its 3 bytes to the 2 written"
            (vector 5 28)
            (tty-handle-write-all-with two-then-three-then-fail h
                                       #vu8(1 2 3 4 5 6 7 8 9 10 11 12)))

;; --- K. the policy of a failed OUTPUT run (imp-2g, F5) -------------
;;
;; tty-glyph-run-policy is the Scheme side of the ONE report seam of
;; src/term.c (m61_tty_output_failed_report).  It takes the plain values
;; of ONE glyph run and answers the plain carrier #(copy-len word): how
;; many bytes of the run the termscript may hold, and what the session
;; tells the user.  The C side reads COPY-LEN, so these checks pin the
;; rule that the 2 streams agree.

;; K1: a complete run.  The whole count moves and the termscript may hold
;; the whole run.
(test-equal "K1 a full run is complete and copies the whole count"
            (vector 12 "complete")
            (tty-glyph-run-policy 12 12 0 #f))

;; K2: a prefix and then a hard failure.  The measured 5 must reach the
;; termscript, NOT the requested 12: a copy of the whole run would make
;; the 2 streams disagree, which is the defect of F5.
(test-equal "K2 a failed run copies its measured prefix, not the length"
            (vector 5 "fatal")
            (tty-glyph-run-policy 5 12 28 #f))

;; K3: an unknown progress.  No byte may be copied, and 0 here is NOT a
;; measurement (F1 and F3 rules).
(test-equal "K3 an unknown progress copies no byte"
            (vector 0 "unknown")
            (tty-glyph-run-policy 0 12 5 #t))

;; K4: a short run with no error.  The measured prefix is known, so it is
;; a "short" run and the prefix may be copied.  A plain 0 progress is NOT
;; inferred from a short count.
(test-equal "K4 a short run with no error is short, not fatal"
            (vector 3 "short")
            (tty-glyph-run-policy 3 12 0 #f))

;; K5: a FULL count AND a hard errno.  The error wins (the imp-2g D4
;; rule), so the run is fatal even when every byte moved.
(test-equal "K5 a hard errno wins over a full count"
            (vector 12 "fatal")
            (tty-glyph-run-policy 12 12 28 #f))

;; K6: a count that is larger than the run can not grant more bytes to the
;; termscript than the run holds.
(test-equal "K6 a count larger than the run is clipped to the length"
            (vector 12 "complete")
            (tty-glyph-run-policy 20 12 0 #f))

;; K7: a REAL EIO with NO byte moved is a hard failure and NOT an unknown
;; progress.  src/term.c keeps the 2 apart with the state flag of the
;; write hub, and not with a heuristic over the count (review cr.org C3):
;; state 3 says "unknown", a real EIO arrives with unknown = #f.  So the
;; fatal-errno policy runs and the copy is the measured 0, not a guess.
(test-equal "K7 a real EIO with no byte moved is fatal, not unknown"
            (vector 0 "fatal")
            (tty-glyph-run-policy 0 12 5 #f))

;; --- the pinned count ----------------------------------------------

;; 1 pass is still to come when this line runs: the pass of this check.
;; So the count here is the pin minus 1, and the exit block below compares
;; the full pin.
(test-assert "Z1 every case ran"
             (= expected-passes (1+ (test-runner-pass-count test-runner))))

;; The summary line and the explicit exit.  The SRFI-64 default exit status
;; is 0 even with an unexpected failure, so a runner that reads the status
;; only would report a green gate for a red suite.  Same shape as the 4
;; sibling suites of this directory: the pin counts every pass, so the
;; compare is (= passes expected-passes).
(let ((passes (test-runner-pass-count test-runner))
      (fails  (test-runner-fail-count test-runner)))
  (format #t "~a: ~a passed, ~a failed (expected ~a passed)~%"
          "Guilemacs tty-handle module" passes fails expected-passes)
  (exit (if (and (zero? fails) (= passes expected-passes)) 0 1)))

(test-end "Guilemacs tty-handle module")
