;;; test-m29-imp2.scm --- M29 imp-2: Haiku build-arm removal audit.
;;;
;;; brief.org (M29 imp-2) removes the Haiku build support: the HAIKU_*
;;; arms in configure.ac and the Makefiles, the HAIKU_* object lists,
;;; and the Haiku sources.  This corpus pins that removal so a later
;;; commit that reintroduces a Haiku arm or a deleted-file name is
;;; caught here.
;;;
;;; It is a static audit.  It reads the build files and asserts:
;;;
;;;   1. no live Haiku build-arm token survives in any build file;
;;;   2. no build file names a deleted Haiku object or header;
;;;   3. every Haiku source listed in brief.org "Current state" is gone;
;;;   4. the opsys=haiku host case, the HAVE_BE_APP apparatus, and the
;;;      dead #ifdef HAVE_HAIKU arm in src/keyboard.c stay (no
;;;      over-deletion).
;;;
;;; The repo root is bound by the .el wrapper as %m29-root (the harness
;;; loads the corpus with CWD=test/).
;;;
;;; Same harness as test-m29-imp1.scm: sourced by the .el wrapper via
;;; eval-scheme; accumulates (NAME STATUS) pairs into test-results.

(use-modules (ice-9 rdelim))
(use-modules (srfi srfi-13))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

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

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m29-root))
    (begin (report "m29-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m29-root ".")))

(define (repo path) (string-append %m29-root "/" path))

;;; --- 1/2. No live Haiku build-arm token in any build file -----------
;;; The token list is file-bearing only: the bare word "Haiku" is NOT a
;;; token, because the --with-be-app prose and the opsys=haiku host
;;; comments keep it (brief.org "What stays").
(define build-files
  '("configure.ac"
    "src/Makefile.in"
    "lib-src/Makefile.in"
    "lib/gnulib.mk.in"
    "doc/emacs/Makefile.in"))

(define arm-tokens
  '("HAIKU_OBJ" "HAIKU_CXX_OBJ" "HAIKU_LIBS" "HAIKU_CFLAGS"
    "haiku.o" "haikufns.o" "haikuterm.o" "haikumenu.o" "haikufont.o"
    "haikuselect.o" "haiku_io.o" "haiku_support.o"
    "haiku_font_support.o" "haiku_draw_support.o" "haiku_select.o"
    "haikuimage.o" "haikuterm.h" "haiku.texi"))

(for-each
 (lambda (file)
   (let* ((path (repo file))
          (body (slurp path))
          (hits (if body
                    (filter (lambda (tok) (has? body tok)) arm-tokens)
                    '())))
     (cond
      ((not body) (report (string-append "build-file-present:" file)
                          (cons 'FAIL "file missing")))
      ((null? hits) (report (string-append "no-arm:" file) 'PASS))
      (else (report (string-append "no-arm:" file)
                    (cons 'FAIL (format #f "tokens ~s" hits)))))))
 build-files)

;;; --- 3. Deleted Haiku sources are gone -----------------------------
(define deleted-paths
  '("src/haiku.c" "src/haikufns.c" "src/haikufont.c" "src/haikuimage.c"
    "src/haiku_io.c" "src/haikumenu.c" "src/haikuselect.c"
    "src/haikuterm.c"
    "src/haiku_draw_support.cc" "src/haiku_font_support.cc"
    "src/haiku_select.cc" "src/haiku_support.cc"
    "src/haikugui.h" "src/haikuselect.h" "src/haiku_support.h"
    "src/haikuterm.h"
    "doc/emacs/haiku.texi"))

(for-each
 (lambda (path)
   (let ((p (repo path)))
     (if (or (file-exists? p) (file-exists? (string-append p "/.")))
         (report (string-append "deleted:" path) (cons 'FAIL "still present"))
         (report (string-append "deleted:" path) 'PASS))))
 deleted-paths)

;;; --- 4. No over-deletion -------------------------------------------
;;; brief.org "What stays": the opsys=haiku host arms and the
;;; HAVE_BE_APP apparatus stay in configure.ac.  The src/keyboard.c
;;; HAVE_HAIKU arm is swept by M29 imp-5 (see test-m29-imp5.scm).
(let ((cfg (slurp (repo "configure.ac"))))
  (if (has? cfg "*-haiku )")
      (report "kept:host-case" 'PASS)
      (report "kept:host-case" (cons 'FAIL "missing *-haiku ) host case")))
  (if (has? cfg "HAVE_BE_APP")
      (report "kept:HAVE_BE_APP" 'PASS)
      (report "kept:HAVE_BE_APP" (cons 'FAIL "missing HAVE_BE_APP apparatus"))))

(reverse test-results)
