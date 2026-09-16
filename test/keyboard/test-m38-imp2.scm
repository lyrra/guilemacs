;;; test-m38-imp2.scm --- M38 imp-2: comment-blind dropped-token scan.
;;;
;;; brief.org (M38 imp-2, defect D2): the m29 dropped-token scan reads
;;; the whole C file, comments included, so the token HAVE_NS matches a
;;; doc comment in src/keyboard.c (added by M36 imp-4) and the run
;;; reddens.  imp-2 makes the scan comment-blind: remove the C comments
;;; from src/keyboard.c before the token scan, and keep the match strict
;;; (whole C identifier).
;;;
;;; Checks:
;;;   1. The repo root is bound by the wrapper (%m38-root).
;;;   2. strip-comments removes a block comment /* ... */.
;;;   3. strip-comments removes a line comment // ... but keeps the
;;;      newline.
;;;   4. strip-comments keeps live code unchanged.
;;;   5. strip-comments keeps the body of a "..." string literal.
;;;   6. Positive control: a token in live code is a hit (the "do not
;;;      weaken" control), and a token is NOT a hit inside a longer
;;;      identifier (HAVE_NS must not match HAVE_NSX).
;;;   7. Negative control: a token in a comment is not a hit.
;;;   8. The stripped src/keyboard.c holds no dropped-platform token.
;;;   9. The raw src/keyboard.c still holds the HAVE_NS doc comment.
;;;  10. Both m29 corpora call their stripper in the dropped-token scan.
;;;  11. The three copies of strip-comments and of ident-hit? do not
;;;      drift: the function bodies compare equal (brief.org §D1,
;;;      review F2).  The call-site check alone cannot catch a changed
;;;      body, so compare the function text too.
;;;
;;; All checks read files or strings, so the corpus is batch-safe.  The
;;; repo root is bound by the .el wrapper as %m38-root.
;;;
;;; The behavior check (the two m29 filters exit 0) runs from the .el
;;; wrapper.  See test/keyboard/test-m38-imp2.el.

(use-modules (ice-9 rdelim))
(use-modules (srfi srfi-13))
(use-modules (srfi srfi-1))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (info name value)
  (report name (list 'INFO value)))

(define (slurp path)
  (if (not (file-exists? path))
      #f
      (call-with-input-file path
        (lambda (port)
          (let loop ((chars '()))
            (let ((c (read-char port)))
              (if (eof-object? c)
                  (list->string (reverse chars))
                  (loop (cons c chars)))))))))

(define (has? s sub)
  (and s (string-contains s sub) #t))

;;; strip-all: remove every occurrence of FROM from S.
(define (strip-all s from)
  (let ((flen (string-length from)))
    (let loop ((start 0) (out '()))
      (let ((idx (string-contains s from start)))
        (if (not idx)
            (string-concatenate
             (reverse (cons (substring s start (string-length s)) out)))
            (loop (+ idx flen)
                  (cons (substring s start idx) out)))))))

;;; strip-comments: return S with every C comment removed and replaced
;;; by one space.  Block comments run from /* to the next */; line
;;; comments run from // to the end of the line (the newline stays).
;;; String ("...") and character ('...') literals are kept, as is a
;;; backslash escape inside either.  A /* inside a string is text, not
;;; a comment start.  Walk the text once with the state CODE, BLOCK,
;;; LINE, STRING, or CHAR.
(define (strip-comments s)
  (let ((n (string-length s)))
    (let loop ((i 0) (state 'code) (out '()))
      (if (>= i n)
          (list->string (reverse out))
          (let ((c (string-ref s i)))
            (define (peek k)
              ;; the character k positions ahead, or #f at the end.
              (let ((j (+ i k)))
                (if (< j n) (string-ref s j) #f)))
            (case state
              ((code)
               (cond
                ((and (char=? c #\/) (eqv? (peek 1) #\*))
                 (loop (+ i 2) 'block (cons #\space out)))
                ((and (char=? c #\/) (eqv? (peek 1) #\/))
                 (loop (+ i 2) 'line (cons #\space out)))
                ((char=? c #\") (loop (+ i 1) 'string (cons c out)))
                ((char=? c #\') (loop (+ i 1) 'char (cons c out)))
                (else (loop (+ i 1) 'code (cons c out)))))
              ((block)
               (if (and (char=? c #\*) (eqv? (peek 1) #\/))
                   (loop (+ i 2) 'code out)
                   (loop (+ i 1) 'block out)))
              ((line)
               (if (char=? c #\newline)
                   (loop (+ i 1) 'code (cons c out))
                   (loop (+ i 1) 'line out)))
              ((string)
               (cond
                ((char=? c #\\)
                 (if (eqv? (peek 1) #f)
                     (loop (+ i 1) 'string (cons c out))
                     (loop (+ i 2) 'string (cons (peek 1) (cons c out)))))
                ((char=? c #\") (loop (+ i 1) 'code (cons c out)))
                (else (loop (+ i 1) 'string (cons c out)))))
              ((char)
               (cond
                ((char=? c #\\)
                 (if (eqv? (peek 1) #f)
                     (loop (+ i 1) 'char (cons c out))
                     (loop (+ i 2) 'char (cons (peek 1) (cons c out)))))
                ((char=? c #\') (loop (+ i 1) 'code (cons c out)))
                (else (loop (+ i 1) 'char (cons c out)))))))))))

;;; ident-hit?: true when TOKEN occurs in S as a whole C identifier.
;;; A whole-identifier match is stricter than the old substring match,
;;; so it cannot hide a live token: HAVE_NS must not match HAVE_NSX.
;;; C identifier characters are [A-Za-z0-9_].
(define (ident-char? c)
  (and c (or (char-alphabetic? c) (char-numeric? c) (char=? c #\_))))

(define (ident-hit? s token)
  (let ((tlen (string-length token))
        (slen (string-length s)))
    (let loop ((start 0))
      (let ((idx (string-contains s token start)))
        (if (not idx)
            #f
            (let ((before (if (= idx 0) #f (string-ref s (- idx 1))))
                  (after (if (>= (+ idx tlen) slen) #f
                             (string-ref s (+ idx tlen)))))
              (if (and (not (ident-char? before)) (not (ident-char? after)))
                  #t
                  (loop (+ idx 1)))))))))

(define (repo path) (string-append %m38-root "/" path))

;;; The dropped-platform token list: the same list the m29 corpora use.
(define kbd-tokens
  '("MSDOS" "WINDOWSNT" "HAVE_NS" "HAIKU" "ANDROID" "DOS_NT" "NTGUI"))

;;; --- 1. The repo root must be known --------------------------------
(if (not (defined? '%m38-root))
    (begin (report "m38/imp2/root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m38-root "."))
    (report "m38/imp2/root-bound" 'PASS))

;;; --- 2. Block comment ----------------------------------------------
(let ((stripped (strip-comments "int x; /* MSDOS */ int y;")))
  (check "m38/imp2/strip/block-comment"
         #t (and (not (has? stripped "MSDOS"))
                 (has? stripped "int x;")
                 (has? stripped "int y;"))))

;;; --- 3. Line comment: // to end of line, newline kept --------------
(let ((stripped (strip-comments "int x; // HAVE_NS\nint y;")))
  (check "m38/imp2/strip/line-comment"
         #t (and (not (has? stripped "HAVE_NS"))
                 (has? stripped "int x;")
                 (has? stripped "int y;")
                 (has? stripped "\n"))))

;;; --- 4. Live code is kept unchanged --------------------------------
(let ((code "int x;\nint y = 3;\n"))
  (check "m38/imp2/strip/ok-keeps-code" code (strip-comments code)))

;;; --- 5. A "..." body is kept, even when it holds a /* --------------
(let ((stripped (strip-comments "s = \"/* MSDOS */\";")))
  (check "m38/imp2/strip/string-kept"
         #t (and (has? stripped "MSDOS")
                 (has? stripped "\"/* MSDOS */\""))))

;;; --- 6. Positive control: a live token is a hit; whole-identifier
;;; match is strict (HAVE_NS does not match HAVE_NSX).  This is the
;;; "do not weaken" control (brief.org exit criterion 2).
(let ((stripped (strip-comments "int x; /* MSDOS */\nint HAVE_NS;\n")))
  (check "m38/imp2/positive/live-token-hits"
         #t (and (ident-hit? stripped "HAVE_NS")
                 (not (ident-hit? stripped "MSDOS")))))
(check "m38/imp2/positive/whole-identifier-strict"
       #f (ident-hit? "int HAVE_NSX;" "HAVE_NS"))

;;; --- 7. Negative control: a token in a comment is not a hit --------
(check "m38/imp2/negative/comment-token-misses"
       #f (ident-hit? (strip-comments "/* HAVE_NS */\n") "HAVE_NS"))

;;; --- 8. The stripped src/keyboard.c is clean ------------------------
(let ((raw (slurp (repo "src/keyboard.c"))))
  (if (not raw)
      (report "m38/imp2/scan/keyboard.c-clean"
              (cons 'FAIL "src/keyboard.c missing"))
      (let* ((stripped (strip-all (strip-comments raw) "FRAME_MSDOS_P"))
             (hits (filter (lambda (tok) (ident-hit? stripped tok))
                           kbd-tokens)))
        (check "m38/imp2/scan/keyboard.c-clean" '() hits)))
  ;; --- 9. The raw file still holds the HAVE_NS doc comment, and the
  ;; stripper removes it.
  (check "m38/imp2/keep/keyboard.c-3878-comment"
         #t (and (has? raw "HAVE_NS and HAVE_PGTK are undefined")
                 (not (has? (strip-comments raw)
                            "HAVE_NS and HAVE_PGTK are undefined")))))

;;; --- 10. Shape: both corpora call their stripper in the scan --------
(define (corpus-calls-stripper? file)
  (let ((body (slurp (repo file))))
    (and body
         (has? body "(strip-all (strip-comments body) \"FRAME_MSDOS_P\")")
         (has? body "(ident-hit? stripped tok)"))))

(check "m38/imp2/shape/imp5-stripper"
       #t (corpus-calls-stripper? "test/keyboard/test-m29-imp5.scm"))
(check "m38/imp2/shape/imp6-stripper"
       #t (corpus-calls-stripper? "test/keyboard/test-m29-imp6.scm"))

;;; --- 11. Drift guard: the three copies of the stripper (and of the
;;; whole-identifier matcher) must stay byte-identical.  The call-site
;;; check in section 10 cannot catch a changed function body, so
;;; compare the function text itself (brief.org §D1, review F2).

;;; define-body: return the source text of the top-level form
;;; (define (NAME ...) ...) in BODY, or #f when the form is absent.
;;; The walk counts parentheses; it skips line comments, string
;;; literals, and character literals.  A character literal consumes
;;; the char after #\, so #\" is not read as a string start.
(define (define-body body name)
  (let* ((marker (string-append "(define (" name))
         (start (and body (string-contains body marker)))
         (n (and body (string-length body))))
    (and start
         (let loop ((i start) (depth 0) (state 'code) (out '()))
           (if (>= i n)
               (list->string (reverse out))
               (let ((c (string-ref body i)))
                 (case state
                   ((code)
                    (cond
                     ((char=? c #\;)
                      (loop (+ i 1) depth 'comment out))
                     ((char=? c #\")
                      (loop (+ i 1) depth 'string (cons c out)))
                     ((and (char=? c #\#) (< (+ i 2) n)
                           (char=? (string-ref body (+ i 1)) #\\))
                      (loop (+ i 3) depth 'code (cons c out)))
                     ((char=? c #\()
                      (loop (+ i 1) (+ depth 1) 'code (cons c out)))
                     ((char=? c #\))
                      (let ((d (- depth 1)))
                        (if (= d 0)
                            (list->string (reverse (cons c out)))
                            (loop (+ i 1) d 'code (cons c out)))))
                     (else (loop (+ i 1) depth 'code (cons c out)))))
                   ((comment)
                    (if (char=? c #\newline)
                        (loop (+ i 1) depth 'code out)
                        (loop (+ i 1) depth 'comment out)))
                   ((string)
                    (cond
                     ((char=? c #\\) (loop (+ i 2) depth 'string out))
                     ((char=? c #\") (loop (+ i 1) depth 'code (cons c out)))
                     (else (loop (+ i 1) depth 'string out)))))))))))

(define (corpus-body file name)
  (define-body (slurp (repo file)) name))

(let ((c5 (corpus-body "test/keyboard/test-m29-imp5.scm" "strip-comments"))
      (c6 (corpus-body "test/keyboard/test-m29-imp6.scm" "strip-comments"))
      (c2 (corpus-body "test/keyboard/test-m38-imp2.scm" "strip-comments")))
  (check "m38/imp2/shape/strip-comments-copies-agree"
         #t (and c5 c6 c2 (string=? c5 c6) (string=? c5 c2))))

(let ((i5 (corpus-body "test/keyboard/test-m29-imp5.scm" "ident-hit?"))
      (i6 (corpus-body "test/keyboard/test-m29-imp6.scm" "ident-hit?"))
      (i2 (corpus-body "test/keyboard/test-m38-imp2.scm" "ident-hit?")))
  (check "m38/imp2/shape/ident-hit-copies-agree"
         #t (and i5 i6 i2 (string=? i5 i6) (string=? i5 i2))))

(reverse test-results)
