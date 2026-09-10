;;; test-m29-imp1.scm --- M29 imp-1: Android build-arm removal audit.
;;;
;;; brief.org (M29 imp-1) removes the Android build support: the arms in
;;; configure.ac and the Makefiles, and the Android sources.  This corpus
;;; pins that removal so a later commit that reintroduces an Android arm
;;; or a deleted-file name is caught here.
;;;
;;; It is a static audit.  It reads the build files and asserts:
;;;
;;;   1. no live Android build-arm token survives in any build file;
;;;   2. no build file names a deleted Android source;
;;;   3. every Android source/dir listed in brief.org "Files to delete"
;;;      is gone;
;;;   4. the two gnulib gl_CHECK_FUNCS_ANDROID calls stay (not over-deleted).
;;;
;;; The repo root is bound by the .el wrapper as %m29-root (the harness
;;; loads the corpus with CWD=test/).
;;;
;;; Same harness as test-m28-imp6.scm: sourced by the .el wrapper via
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

;;; --- 1. No live Android build-arm token in any build file -----------
;;; Tokens chosen so that allowed prose and the gnulib
;;; gl_CHECK_FUNCS_ANDROID calls never match.
(define build-files
  '("configure.ac"
    "Makefile.in"
    "src/Makefile.in"
    "lib/Makefile.in"
    "lib/gnulib.mk.in"
    "lib-src/Makefile.in"
    "src/epaths.in"
    "src/verbose.mk.in"
    "doc/emacs/Makefile.in"
    "doc/emacs/emacs.texi"))

(define arm-tokens
  '("XCONFIGURE" "REALLY_ANDROID"
    "ANDROID_OBJ" "ANDROID_LIBS" "ANDROID_LDFLAGS" "ANDROID_BUILD_CFLAGS"
    "ANDROID_CFLAGS" "ANDROID_SDK" "ANDROID_ABI" "ANDROID_JAR"
    "ANDROID_SHARED_USER" "ANDROID_DEBUGGABLE"
    "ndk_INIT" "ndk_LATE" "ndk_SEARCH_MODULE" "ndk_CHECK_MODULES"
    "ndk_CONFIG_FILES" "NDK_BUILD_" "android_makefiles"
    "asset-directory-tool" "sfntfont-android"
    "androidterm.o" "androidfns.o" "androidfont.o"
    "androidselect" "androidvfs" "AndroidManifest" "android.texi"
    ;; Dangling @VAR@ substitutions whose only definition lived in the
    ;; Android block (cr.org F1): SDK_BUILD_TOOLS, WARN_JAVAFLAGS, ZIP,
    ;; emacs_use_mailutils.
    "@SDK_BUILD_TOOLS@" "@WARN_JAVAFLAGS@" "@ZIP@" "@emacs_use_mailutils@"))

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

;;; --- 2/3. Deleted Android sources and directories are gone ----------
(define deleted-paths
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

(for-each
 (lambda (path)
   (let ((p (repo path)))
     (if (or (file-exists? p) (file-exists? (string-append p "/.")))
         (report (string-append "deleted:" path) (cons 'FAIL "still present"))
         (report (string-append "deleted:" path) 'PASS))))
 deleted-paths)

;;; --- 4. The gnulib Android macro calls stay ------------------------
;;; brief.org "What stays": the gl_CHECK_FUNCS_ANDROID calls are gnulib,
;;; not Emacs build support.  A removal here means we over-deleted.
(let ((cfg (slurp (repo "configure.ac"))))
  (for-each
   (lambda (call)
     (if (has? cfg call)
         (report (string-append "gnulib-kept:" call) 'PASS)
         (report (string-append "gnulib-kept:" call) (cons 'FAIL "missing"))))
   '("gl_CHECK_FUNCS_ANDROID([getpwent]"
     "gl_CHECK_FUNCS_ANDROID([renameat2]")))

(reverse test-results)
