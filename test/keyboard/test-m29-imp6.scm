;;; test-m29-imp6.scm --- M29 imp-6: close-out audit.
;;;
;;; brief.org (M29 imp-6) is the close-out step of M29.  It ports no
;;; code and changes no C file.  It verifies the dropped-platform
;;; removal that imp-1 (Android), imp-2 (Haiku), imp-3 (W32 /
;;; Cygwin), imp-4 (MS-DOS), and imp-5 (the src/keyboard.c sweep)
;;; performed, and it pins the M29 end state so a later commit that
;;; reintroduces a dropped-platform path, build-arm name, or
;;; dropped-platform token is caught here.
;;;
;;; NS stays out of scope: the tree still holds src/ns*.m, src/ns*.h,
;;; and nextstep/.  M29 removes W32, Cygwin, Haiku, Android, and
;;; MS-DOS only.  (milestone.org §Goal is corrected to match.)
;;;
;;; This corpus is a static audit.  It reads the tree and asserts:
;;;
;;;   1. the repo root is bound (%m29-root);
;;;   2. no dropped-platform path exists -- the deleted-path lists of
;;;      the imp-1 .. imp-4 corpora plus the seven runtime leftovers;
;;;   3. no live build file names a dropped-platform source file
;;;      (file-bearing tokens only; the bare opsys words mingw32 /
;;;      cygwin / haiku stay, because configure.ac keeps them);
;;;   4. src/keyboard.c keeps no dropped-platform token (MSDOS,
;;;      WINDOWSNT, HAVE_NS, HAIKU, ANDROID, DOS_NT, NTGUI), after the
;;;      kept inert FRAME_MSDOS_P name is stripped;
;;;   5. the config-variance arms stay: USE_TOOLKIT_SCROLL_BARS,
;;;      HAVE_X_WINDOWS, HAVE_TEXT_CONVERSION;
;;;   6. the imp-5 sweep result stays: the four dropped DEFSYMs and
;;;      the dropped event kinds are gone, FUNCTION_KEY_OFFSET stays
;;;      at 0xff00, and the lispy_function_keys[] table stays;
;;;   7. no over-deletion: AH_TEMPLATE([MSDOS]) stays in configure.ac,
;;;      the cygwin / mingw32 / haiku opsys cases stay, nextstep/
;;;      stays, and FRAME_MSDOS_P stays in src/keyboard.c;
;;;   8. the remnant line counts are printed (status INFO), not
;;;      asserted.
;;;
;;; The repo root is bound by the .el wrapper as %m29-root (the
;;; harness loads the corpus with CWD=test/).
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test
;;; and prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m29-imp6.el.

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

;;; count-lines: the number of newline characters in S (wc -l).
(define (count-lines path)
  (let ((body (slurp path)))
    (if (not body)
        #f
        (let loop ((i 0) (n 0))
          (if (>= i (string-length body))
              n
              (loop (+ i 1)
                    (if (char=? (string-ref body i) #\newline)
                        (+ n 1) n)))))))

;;; --- 1. The repo root must be known --------------------------------
(if (not (defined? '%m29-root))
    (begin (report "m29-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m29-root "."))
    (report "m29-root-bound" 'PASS))

(define (repo path) (string-append %m29-root "/" path))

(define (gone? path)
  (let ((full (repo path)))
    (not (or (file-exists? full) (file-exists? (string-append full "/."))))))

(define (check-gone label paths)
  (let ((present (filter (lambda (p) (not (gone? p))) paths)))
    (if (null? present)
        (report label 'PASS)
        (report label (cons 'FAIL (format #f "still present ~s" present))))))

;;; --- 2. No dropped-platform path exists ----------------------------
;;; The lists are the deleted-path lists of the imp-1 .. imp-4 corpora
;;; plus the seven runtime leftovers swept at imp-5.
(define android-paths
  '("src/android.c" "src/android-emacs.c" "src/androidfns.c"
    "src/androidfont.c" "src/androidmenu.c" "src/androidselect.c"
    "src/androidterm.c" "src/androidvfs.c"
    "src/android.h" "src/android-asset.h" "src/androidgui.h"
    "src/androidterm.h" "src/sfntfont-android.c"
    "lib-src/asset-directory-tool.c"
    "m4/ndk-build.m4"
    "build-aux/ndk-build-helper.mk" "build-aux/ndk-build-helper-1.mk"
    "build-aux/ndk-build-helper-2.mk" "build-aux/ndk-build-helper-3.mk"
    "build-aux/ndk-build-helper-4.mk" "build-aux/ndk-module-extract.awk"
    "doc/emacs/android.texi"
    "java" "cross"))

(define haiku-paths
  '("src/haiku.c" "src/haikufns.c" "src/haikufont.c" "src/haikuimage.c"
    "src/haiku_io.c" "src/haikumenu.c" "src/haikuselect.c"
    "src/haikuterm.c"
    "src/haiku_draw_support.cc" "src/haiku_font_support.cc"
    "src/haiku_select.cc" "src/haiku_support.cc"
    "src/haikugui.h" "src/haikuselect.h" "src/haiku_support.h"
    "src/haikuterm.h"
    "doc/emacs/haiku.texi"))

(define w32-paths
  '("src/w32.c" "src/w32.h" "src/w32common.h" "src/w32console.c"
    "src/w32cygwinx.c" "src/w32dwrite.c" "src/w32fns.c" "src/w32font.c"
    "src/w32font.h" "src/w32gdiplus.h" "src/w32gui.h" "src/w32heap.c"
    "src/w32heap.h" "src/w32image.c" "src/w32inevt.c" "src/w32inevt.h"
    "src/w32menu.c" "src/w32notify.c" "src/w32proc.c" "src/w32reg.c"
    "src/w32select.c" "src/w32select.h" "src/w32term.c" "src/w32term.h"
    "src/w32uniscribe.c" "src/w32xfns.c"
    "src/cygw32.c" "src/cygw32.h" "lib-src/ntlib.c" "lib-src/ntlib.h"
    "build-aux/msys-to-w32" "nt"))

(define msdos-paths
  '("src/msdos.c" "src/msdos.h" "src/dosfns.c" "src/dosfns.h"
    "src/w16select.c" "msdos" "doc/emacs/msdos.texi"
    "doc/emacs/msdos-xtra.texi"))

(define leftover-paths
  '("lisp/w32-vars.el" "lisp/w32-fns.el" "lisp/dos-w32.el"
    "lisp/term/w32console.el" "lisp/term/w32-win.el"
    "lisp/term/cygwin.el" "etc/w32-feature.el"))

(check-gone "gone:android" android-paths)
(check-gone "gone:haiku" haiku-paths)
(check-gone "gone:w32-cygwin" w32-paths)
(check-gone "gone:msdos" msdos-paths)
(check-gone "gone:runtime-leftovers" leftover-paths)

;;; --- 3. No live build file names a dropped-platform source ---------
;;; File-bearing tokens only.  The bare opsys words mingw32, cygwin,
;;; and haiku are NOT tokens: configure.ac keeps its host detection.
(define build-files
  '("configure.ac"
    "Makefile.in"
    "src/Makefile.in"
    "lib-src/Makefile.in"
    "lib/gnulib.mk.in"
    "doc/misc/Makefile.in"
    "lisp/Makefile.in"
    "lisp/loadup.el"
    "lisp/ldefs-boot.el"
    "src/deps.mk"
    "src/epaths.in"
    "src/verbose.mk.in"
    "test/Makefile.in"))

(define dropped-name-tokens
  '("w32term.c" "w32term.h" "w32fns.c" "w32font.c" "w32font.h"
    "w32gui.h" "w32heap.c" "w32heap.h" "w32image.c" "w32inevt.c"
    "w32inevt.h" "w32menu.c" "w32notify.c" "w32proc.c" "w32reg.c"
    "w32select.c" "w32select.h" "w32uniscribe.c" "w32xfns.c"
    "w32console.c" "w32cygwinx.c" "w32dwrite.c" "w32gdiplus.h"
    "w32common.h" "w32.h" "w32.c"
    "cygw32.c" "cygw32.h" "ntlib.c" "ntlib.h" "msys-to-w32"
    "msdos.c" "msdos.h" "dosfns.c" "dosfns.h" "w16select.c"
    "msdos.o" "dosfns.o" "w16select.o"
    "msdos.texi" "msdos-xtra.texi"
    "haiku.c" "haikufns.c" "haikufont.c" "haikuimage.c" "haiku_io.c"
    "haikumenu.c" "haikuselect.c" "haikuterm.c" "haikuterm.h"
    "haiku_draw_support.cc" "haiku_font_support.cc" "haiku_select.cc"
    "haiku_support.cc" "haikugui.h" "haikuselect.h" "haiku_support.h"
    "haiku.texi"
    "android.c" "androidfns.c" "androidfont.c" "androidmenu.c"
    "androidselect.c" "androidterm.c" "androidvfs.c" "androidterm.h"
    "androidgui.h" "android.h" "android-asset.h" "sfntfont-android.c"
    "asset-directory-tool.c" "ndk-build.m4" "android.texi"
    "w32-vars" "w32-fns" "dos-w32" "w32console" "w32-win" "cygwin.el"
    "w32-feature"
    "emacs.res" "emacsclientw" "epaths-force-w32"))

(for-each
 (lambda (file)
   (let* ((path (repo file))
          (body (slurp path))
          (hits (if body
                    (filter (lambda (tok) (has? body tok))
                            dropped-name-tokens)
                    '())))
     (cond
      ((not body) (report (string-append "build-file-present:" file)
                          (cons 'FAIL "file missing")))
      ((null? hits) (report (string-append "no-dropped-name:" file) 'PASS))
      (else (report (string-append "no-dropped-name:" file)
                    (cons 'FAIL (format #f "tokens ~s" hits)))))))
 build-files)

;;; --- 4. src/keyboard.c keeps no dropped-platform token -------------
;;; FRAME_MSDOS_P is an inert frame macro (brief.org "What stays"), not
;;; an #ifdef arm, so it is stripped before the scan.
(define kbd-tokens
  '("MSDOS" "WINDOWSNT" "HAVE_NS" "HAIKU" "ANDROID" "DOS_NT" "NTGUI"))

(let ((body (slurp (repo "src/keyboard.c"))))
  (if (not body)
      (report "kbd:present" (cons 'FAIL "src/keyboard.c missing"))
      (let* ((stripped (strip-all body "FRAME_MSDOS_P"))
             (hits (filter (lambda (tok) (has? stripped tok)) kbd-tokens)))
        (if (null? hits)
            (report "kbd:no-dropped-token" 'PASS)
            (report "kbd:no-dropped-token"
                    (cons 'FAIL (format #f "tokens ~s" hits)))))))

;;; --- 5. Config-variance arms survive -------------------------------
(define kept-arms
  '("USE_TOOLKIT_SCROLL_BARS" "HAVE_X_WINDOWS" "HAVE_TEXT_CONVERSION"))

(let ((body (slurp (repo "src/keyboard.c"))))
  (for-each
   (lambda (tok)
     (if (has? body tok)
         (report (string-append "kbd:kept-arm:" tok) 'PASS)
         (report (string-append "kbd:kept-arm:" tok)
                 (cons 'FAIL "config-variance arm gone (over-deleted)"))))
   kept-arms))

;;; --- 6. The imp-5 sweep result stays -------------------------------
(define kbd-body (slurp (repo "src/keyboard.c")))

;;; The four dropped DEFSYMs and the live dropped event-kind constants.
;;; The string MULTIMEDIA_KEY_EVENT is NOT a token: it survives only in
;;; the doc comment of the kept --lispy-multimedia-keys DEFUN (it
;;; explains why that DEFUN returns an empty vector).
(define kbd-gone
  '("Qmultimedia_key" "Qlanguage_change" "Qend_session"
    "Qnotification_event" "END_SESSION_EVENT" "LANGUAGE_CHANGE_EVENT"
    "NOTIFICATION_EVENT"))

(let ((hits (filter (lambda (tok) (has? kbd-body tok)) kbd-gone)))
  (if (null? hits)
      (report "kbd:swept-defsyms-events" 'PASS)
      (report "kbd:swept-defsyms-events"
              (cons 'FAIL (format #f "tokens ~s" hits)))))

(if (has? kbd-body "#define FUNCTION_KEY_OFFSET 0xff00")
    (report "kbd:FUNCTION_KEY_OFFSET-0xff00" 'PASS)
    (report "kbd:FUNCTION_KEY_OFFSET-0xff00"
            (cons 'FAIL "FUNCTION_KEY_OFFSET is not 0xff00")))

(if (and (has? kbd-body "lispy_function_keys[] =")
         (has? kbd-body "\"backspace\""))
    (report "kbd:lispy_function_keys-present" 'PASS)
    (report "kbd:lispy_function_keys-present"
            (cons 'FAIL "X keysym lispy_function_keys table gone")))

;;; --- 7. No over-deletion -------------------------------------------
(let ((cfg (slurp (repo "configure.ac"))))
  (if (not cfg)
      (report "configure.ac-present" (cons 'FAIL "configure.ac missing"))
      (begin
        (if (has? cfg "AH_TEMPLATE([MSDOS]")
            (report "kept:AH_TEMPLATE-MSDOS" 'PASS)
            (report "kept:AH_TEMPLATE-MSDOS"
                    (cons 'FAIL "AH_TEMPLATE([MSDOS]) gone (over-deleted)")))
        (if (has? cfg "*-*-cygwin )")
            (report "kept:opsys-cygwin" 'PASS)
            (report "kept:opsys-cygwin"
                    (cons 'FAIL "opsys cygwin case gone (over-deleted)")))
        (if (has? cfg "opsys=mingw32")
            (report "kept:opsys-mingw32" 'PASS)
            (report "kept:opsys-mingw32"
                    (cons 'FAIL "opsys mingw32 case gone (over-deleted)")))
        (if (has? cfg "*-haiku )")
            (report "kept:opsys-haiku" 'PASS)
            (report "kept:opsys-haiku"
                    (cons 'FAIL "opsys haiku case gone (over-deleted)"))))))

(if (file-exists? (repo "nextstep"))
    (report "kept:nextstep" 'PASS)
    (report "kept:nextstep" (cons 'FAIL "nextstep/ gone (over-deleted)")))

(if (has? kbd-body "FRAME_MSDOS_P")
    (report "kept:FRAME_MSDOS_P" 'PASS)
    (report "kept:FRAME_MSDOS_P"
            (cons 'FAIL "FRAME_MSDOS_P gone (over-deleted)")))

;;; --- 8. Remnant counts (INFO; printed, not asserted) ---------------
(define kbd-lines (count-lines (repo "src/keyboard.c")))
(define kg-lines (count-lines (repo "src/keyboard-globals.c")))
(define combined
  (if (and kbd-lines kg-lines) (+ kbd-lines kg-lines) #f))

(report "remnant:src/keyboard.c-lines" (list 'INFO kbd-lines))
(report "remnant:src/keyboard-globals.c-lines" (list 'INFO kg-lines))
(report "remnant:combined-lines" (list 'INFO combined))

(reverse test-results)
