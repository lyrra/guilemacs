;;; test-m29-imp4.scm --- M29 imp-4: MS-DOS build-arm removal audit.
;;;
;;; brief.org (M29 imp-4) removes the MS-DOS build support: the
;;; MSDOS_OBJ / MSDOS_X_OBJ arms in src/Makefile.in, the base_obj
;;; reference, the SOME_MACHINE_OBJECTS entries (dosfns.o, msdos.o,
;;; w16select.o), the three .x rules, the msdos/sed1v2.inp note, and the
;;; two EXTRA_DIST entries plus the two @include lines in the doc/emacs
;;; files.  It deletes src/msdos.{c,h}, src/dosfns.{c,h},
;;; src/w16select.c, the whole msdos/ directory, and
;;; doc/emacs/msdos.texi / msdos-xtra.texi, and fixes the msdos/
;;; cross-references in doc/misc/efaq.texi and doc/misc/efaq-w32.texi.
;;; This corpus pins that removal so a later commit that reintroduces an
;;; MS-DOS arm or a deleted-file name is caught here.
;;;
;;; It is a static audit.  It reads the build files and asserts:
;;;
;;;   1. no live MS-DOS build-arm token survives in src/Makefile.in,
;;;      doc/emacs/Makefile.in, doc/emacs/emacs.texi, or
;;;      doc/emacs/emacs-xtra.texi;
;;;   2. no build file names a deleted MS-DOS file;
;;;   3. every path deleted in brief.org Step 3 is gone;
;;;   4. no over-deletion: AH_TEMPLATE([MSDOS]) stays in configure.ac,
;;;      src/keyboard.c keeps its DOS_NT and HAVE_X_WINDOWS arms,
;;;      doc/misc/efaq-w32.texi keeps its node "Other versions of Emacs"
;;;      and @xref{Cygwin}, and nextstep/ stays;
;;;   5. brief.org Step 4: the stale msdos/ cross-references are gone
;;;      from doc/misc/efaq.texi and doc/misc/efaq-w32.texi, and the
;;;      nextstep/INSTALL line stays.
;;;
;;; The repo root is bound by the .el wrapper as %m29-root (the harness
;;; loads the corpus with CWD=test/).
;;;
;;; Same harness as test-m29-imp3.scm: sourced by the .el wrapper via
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

;;; --- 1. No live MS-DOS build-arm token in the four build/doc files
;;; The token list is file-bearing only: the bare words "msdos" and
;;; "MSDOS" are NOT tokens, because configure.ac keeps
;;; AH_TEMPLATE([MSDOS]) and the shared C files keep the dead #ifdef
;;; arms (brief.org "What stays").
(define arm-files
  '("src/Makefile.in"
    "doc/emacs/Makefile.in"
    "doc/emacs/emacs.texi"
    "doc/emacs/emacs-xtra.texi"))

(define arm-tokens
  '("MSDOS_OBJ" "MSDOS_X_OBJ" "dosfns.o" "msdos.o" "w16select.o"
    "dosfns.x" "msdos.x" "w16select.x"
    "msdos/sed1v2.inp" "msdos-xtra.texi" "msdos.texi"))

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
 arm-files)

;;; --- 2. No build file names a deleted MS-DOS file ------------------
;;; The token list is file-bearing only.  configure.ac keeps the MSDOS
;;; macro template, which is not a file name, so it is not a token.
(define build-files
  '("configure.ac"
    "Makefile.in"
    "src/Makefile.in"
    "lib-src/Makefile.in"
    "doc/emacs/Makefile.in"
    "doc/misc/Makefile.in"
    "lib/gnulib.mk.in"
    "lisp/Makefile.in"
    "test/Makefile.in"))

(define deleted-name-tokens
  '("msdos.c" "msdos.h" "dosfns.c" "dosfns.h" "w16select.c"
    "msdos/" "msdos.texi" "msdos-xtra.texi"))

(for-each
 (lambda (file)
   (let* ((path (repo file))
          (body (slurp path))
          (hits (if body
                    (filter (lambda (tok) (has? body tok)) deleted-name-tokens)
                    '())))
     (cond
      ((not body) (report (string-append "build-file-present:" file)
                          (cons 'FAIL "file missing")))
      ((null? hits) (report (string-append "no-deleted-name:" file) 'PASS))
      (else (report (string-append "no-deleted-name:" file)
                    (cons 'FAIL (format #f "tokens ~s" hits)))))))
 build-files)

;;; --- 3. Deleted MS-DOS paths are gone ------------------------------
(define deleted-paths
  '("src/msdos.c" "src/msdos.h" "src/dosfns.c" "src/dosfns.h"
    "src/w16select.c" "msdos" "doc/emacs/msdos.texi"
    "doc/emacs/msdos-xtra.texi"))

(for-each
 (lambda (path)
   (let ((p (repo path)))
     (if (or (file-exists? p) (file-exists? (string-append p "/.")))
         (report (string-append "deleted:" path) (cons 'FAIL "still present"))
         (report (string-append "deleted:" path) 'PASS))))
 deleted-paths)

;;; --- 4. No over-deletion -------------------------------------------
;;; brief.org "What stays": AH_TEMPLATE([MSDOS]) stays in configure.ac;
;;; src/keyboard.c keeps its config-variance HAVE_X_WINDOWS arm (imp-5
;;; sweeps the dropped-platform DOS_NT arms; see test-m29-imp5);
;;; doc/misc/efaq-w32.texi keeps the node "Other versions of Emacs" and
;;; its @xref{Cygwin}; nextstep/ stays.
(let ((cfg (slurp (repo "configure.ac"))))
  (if (has? cfg "AH_TEMPLATE([MSDOS]")
      (report "kept:AH_TEMPLATE-MSDOS" 'PASS)
      (report "kept:AH_TEMPLATE-MSDOS"
              (cons 'FAIL "AH_TEMPLATE([MSDOS]) gone (over-deleted)"))))

(let ((kbd (slurp (repo "src/keyboard.c"))))
  (if (has? kbd "HAVE_X_WINDOWS")
      (report "kept:keyboard.c-HAVE_X_WINDOWS-arm" 'PASS)
      (report "kept:keyboard.c-HAVE_X_WINDOWS-arm"
              (cons 'FAIL "keyboard.c HAVE_X_WINDOWS arm gone (over-deleted)"))))

(let ((w32 (slurp (repo "doc/misc/efaq-w32.texi"))))
  (if (has? w32 "@node Other versions of Emacs")
      (report "kept:efaq-w32-node" 'PASS)
      (report "kept:efaq-w32-node"
              (cons 'FAIL "efaq-w32 node gone (over-deleted)")))
  (if (has? w32 "@xref{Cygwin}")
      (report "kept:efaq-w32-cygwin-xref" 'PASS)
      (report "kept:efaq-w32-cygwin-xref"
              (cons 'FAIL "efaq-w32 @xref{Cygwin} gone (over-deleted)"))))

(if (file-exists? (repo "nextstep"))
    (report "kept:nextstep" 'PASS)
    (report "kept:nextstep" (cons 'FAIL "nextstep/ gone (over-deleted)")))

;;; --- 5. Step-4 doc cross-references are fixed ----------------------
;;; brief.org Step 4: delete the stale msdos/ path in doc/misc/efaq.texi
;;; and doc/misc/efaq-w32.texi, and keep every live section.  The token
;;; list is file-bearing or index-bearing; the bare words "MS-DOS" and
;;; "Windows" stay, because other sections keep them.
(define efaq-stale
  '("@file{msdos/INSTALL}"
    "@cindex MS-DOS, Emacs for"
    "@cindex DOS, Emacs for"
    "@cindex Compiling Emacs for DOS"
    "@cindex Emacs for MS-DOS"
    "delorie.com/pub/djgpp"))

(let ((body (slurp (repo "doc/misc/efaq.texi"))))
  (if (not body)
      (report "doc-xref:efaq.texi-present" (cons 'FAIL "file missing"))
      (let ((hits (filter (lambda (tok) (has? body tok)) efaq-stale)))
        (if (null? hits)
            (report "doc-xref:efaq.texi" 'PASS)
            (report "doc-xref:efaq.texi"
                    (cons 'FAIL (format #f "stale tokens ~s" hits)))))))

(define efaq-w32-stale
  '("@cindex DOS port"
    "@cindex Windows 3.11 port"
    "@file{msdos}"))

(let ((body (slurp (repo "doc/misc/efaq-w32.texi"))))
  (if (not body)
      (report "doc-xref:efaq-w32.texi-present" (cons 'FAIL "file missing"))
      (let ((hits (filter (lambda (tok) (has? body tok)) efaq-w32-stale)))
        (if (null? hits)
            (report "doc-xref:efaq-w32.texi" 'PASS)
            (report "doc-xref:efaq-w32.texi"
                    (cons 'FAIL (format #f "stale tokens ~s" hits)))))))

;;; No over-deletion in the cross-reference fix: the nextstep/INSTALL
;;; line above the deleted MS-DOS paragraph stays (nextstep/ stays).
(let ((body (slurp (repo "doc/misc/efaq.texi"))))
  (if (has? body "@file{nextstep/INSTALL}")
      (report "kept:efaq-nextstep" 'PASS)
      (report "kept:efaq-nextstep"
              (cons 'FAIL "@file{nextstep/INSTALL} gone (over-deleted)"))))

(reverse test-results)
