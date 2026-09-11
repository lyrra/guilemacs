;;; test-m29-imp3.scm --- M29 imp-3: W32 / Cygwin build-arm removal audit.
;;;
;;; brief.org (M29 imp-3) removes the W32 and Cygwin build support: the
;;; W32_* / CYGWIN_OBJ / DOCMISC_W32 arms in configure.ac and the
;;; Makefiles, the W32 object lists and .x rules, the epaths-force-w32
;;; rule, and the src/w32* sources, src/cygw32.c, src/cygw32.h, nt/, and
;;; the dead lib-src/ntlib.{c,h} leftovers.  This corpus pins that
;;; removal so a later commit that reintroduces a W32 arm or a
;;; deleted-file name is caught here.
;;;
;;; It is a static audit.  It reads the build files and asserts:
;;;
;;;   1. no live W32 / Cygwin build-arm token survives in any build file;
;;;   2. no build file names a deleted W32 file or an nt/ path;
;;;   3. every path deleted in brief.org Step 2 is gone;
;;;   4. no over-deletion: the opsys cygwin / mingw32 host cases stay,
;;;      HAVE_W32=no stays, and the dead HAVE_NTGUI / DOS_NT arms in
;;;      src/keyboard.c and doc/emacs/msdos.texi stay.
;;;
;;; The repo root is bound by the .el wrapper as %m29-root (the harness
;;; loads the corpus with CWD=test/).
;;;
;;; Same harness as test-m29-imp2.scm: sourced by the .el wrapper via
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

;;; --- 1/2. No live W32 / Cygwin build-arm token, deleted-file name, or
;;;          nt/ path in any build file -------------------------------
;;; The token list is file-bearing only: the bare words "w32" and
;;; "cygwin" are NOT tokens, because the opsys host cases and the efaq-w32
;;; texinfo entry keep them (brief.org "What stays" and "Open points").
(define build-files
  '("configure.ac"
    "Makefile.in"
    "src/Makefile.in"
    "lib-src/Makefile.in"
    "lib/gnulib.mk.in"
    "doc/misc/Makefile.in"
    "lisp/Makefile.in"))

(define arm-tokens
  '("W32_OBJ" "W32_LIBS" "W32_RES_LINK" "EMACSRES" "CLIENTRES" "CLIENTW"
    "EMACS_MANIFEST" "FIRSTFILE_OBJ" "CM_OBJ" "LIBS_ECLIENT"
    "LIB_WSOCK32" "NTLIB" "XARGS_LIMIT" "CYGWIN_OBJ" "DOCMISC_W32"
    "NTDIR" "NTINC" "NTDEPS" "WINDRES" "HAVE_NTGUI" "epaths-force-w32"
    ;; deleted W32 / Cygwin object and source names
    "cygw32.o" "cygw32.c" "cygw32.h" "ntlib.o" "ntlib.c" "ntlib.h"
    "emacs.res" "emacsclientw"
    "w32cygwinx.o" "w32fns.o" "w32.o"
    "w32.c" "w32.h" "w32common.h" "w32console.c" "w32cygwinx.c"
    "w32dwrite.c" "w32fns.c" "w32font.c" "w32font.h" "w32gdiplus.h"
    "w32gui.h" "w32heap.c" "w32heap.h" "w32image.c" "w32inevt.c"
    "w32inevt.h" "w32menu.c" "w32notify.c" "w32proc.c" "w32reg.c"
    "w32select.c" "w32select.h" "w32term.c" "w32term.h" "w32uniscribe.c"
    "w32xfns.c"
    ;; deleted nt/ paths and the W32-only helper
    "nt/epaths.nt" "nt/inc" "nt/mingw-cfg.site" "nt/Makefile"
    "nt/emacs.rc.in" "nt/emacsclient.rc.in" "msys-to-w32"))

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

;;; --- 3. Deleted W32 / Cygwin paths are gone -------------------------
(define deleted-paths
  '("src/w32.c" "src/w32.h" "src/w32common.h" "src/w32console.c"
    "src/w32cygwinx.c" "src/w32dwrite.c" "src/w32fns.c" "src/w32font.c"
    "src/w32font.h" "src/w32gdiplus.h" "src/w32gui.h" "src/w32heap.c"
    "src/w32heap.h" "src/w32image.c" "src/w32inevt.c" "src/w32inevt.h"
    "src/w32menu.c" "src/w32notify.c" "src/w32proc.c" "src/w32reg.c"
    "src/w32select.c" "src/w32select.h" "src/w32term.c" "src/w32term.h"
    "src/w32uniscribe.c" "src/w32xfns.c"
    "src/cygw32.c" "src/cygw32.h" "lib-src/ntlib.c" "lib-src/ntlib.h"
    "build-aux/msys-to-w32" "nt"))

(for-each
 (lambda (path)
   (let ((p (repo path)))
     (if (or (file-exists? p) (file-exists? (string-append p "/.")))
         (report (string-append "deleted:" path) (cons 'FAIL "still present"))
         (report (string-append "deleted:" path) 'PASS))))
 deleted-paths)

;;; --- 4. No over-deletion -------------------------------------------
;;; brief.org "What stays": the opsys cygwin / mingw32 host cases and
;;; HAVE_W32=no stay in configure.ac.  src/keyboard.c is unchanged; its
;;; HAVE_NTGUI / DOS_NT arms stay (imp-5 sweeps them).  doc/emacs/msdos.texi
;;; stays (imp-4 removes it).
(let ((cfg (slurp (repo "configure.ac"))))
  (if (has? cfg "*-*-cygwin )")
      (report "kept:host-case-cygwin" 'PASS)
      (report "kept:host-case-cygwin" (cons 'FAIL "missing *-*-cygwin ) host case")))
  (if (has? cfg "opsys=mingw32")
      (report "kept:host-case-mingw32" 'PASS)
      (report "kept:host-case-mingw32" (cons 'FAIL "missing opsys=mingw32 host case")))
  (if (has? cfg "HAVE_W32=no")
      (report "kept:HAVE_W32=no" 'PASS)
      (report "kept:HAVE_W32=no" (cons 'FAIL "missing HAVE_W32=no"))))

(let ((kbd (slurp (repo "src/keyboard.c"))))
  (if (has? kbd "HAVE_NTGUI")
      (report "kept:keyboard.c-HAVE_NTGUI-arm" 'PASS)
      (report "kept:keyboard.c-HAVE_NTGUI-arm"
              (cons 'FAIL "keyboard.c HAVE_NTGUI arm gone (over-deleted)")))
  (if (has? kbd "DOS_NT")
      (report "kept:keyboard.c-DOS_NT-arm" 'PASS)
      (report "kept:keyboard.c-DOS_NT-arm"
              (cons 'FAIL "keyboard.c DOS_NT arm gone (over-deleted)"))))

(if (file-exists? (repo "doc/emacs/msdos.texi"))
    (report "kept:doc/emacs/msdos.texi" 'PASS)
    (report "kept:doc/emacs/msdos.texi" (cons 'FAIL "msdos.texi gone (over-deleted)")))

(reverse test-results)
