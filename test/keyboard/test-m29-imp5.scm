;;; test-m29-imp5.scm --- M29 imp-5: dropped-platform sweep audit.
;;;
;;; brief.org (M29 imp-5) is the sweep step of M29.  It removes the
;;; dropped-platform code that imp-1 (Android), imp-2 (Haiku), imp-3
;;; (W32 / Cygwin) and imp-4 (MS-DOS) left behind in the shared tree:
;;;
;;;   * every dropped-platform #ifdef arm and dead dropped-platform doc
;;;     comment in src/keyboard.c;
;;;   * the dead guarded includes in src/emacs.c and lib-src/*;
;;;   * seven runtime Lisp / etc leftovers and their load-path
;;;     references (loadup.el, ldefs-boot.el);
;;;   * the dropped-platform comments in mod/emacs/*.scm.
;;;
;;; This corpus pins that sweep so a later commit that reintroduces a
;;; dropped-platform token or a deleted path is caught here.
;;;
;;; It is a static audit.  It reads the tree and asserts:
;;;
;;;   1. no dropped-platform token survives in src/keyboard.c (tokens
;;;      MSDOS, WINDOWSNT, HAVE_NS, HAIKU, ANDROID, DOS_NT, NTGUI),
;;;      after stripping the kept inert FRAME_MSDOS_P macro name;
;;;   2. every config-variance arm survives: USE_TOOLKIT_SCROLL_BARS,
;;;      HAVE_X_WINDOWS, HAVE_TEXT_CONVERSION;
;;;   3. every Lisp / etc path deleted by brief.org Step 3 is gone;
;;;   4. no live build file names a deleted path: lisp/loadup.el,
;;;      lisp/ldefs-boot.el, lisp/loaddefs.el (generated; skipped when
;;;      absent), lisp/Makefile.in;
;;;   5. no over-deletion: configure.ac keeps AH_TEMPLATE([MSDOS]) and
;;;      the cygwin / mingw32 opsys cases; src/keyboard.c keeps
;;;      FRAME_MSDOS_P;
;;;   6. the keyboard.c sweep results: the four dropped DEFSYMs and the
;;;      two dropped event kinds are gone, and the lispy_function_keys
;;;      collapse yields the X keysym table at FUNCTION_KEY_OFFSET 0xff00;
;;;   7. lisp/loadup.el keeps the supported ns block;
;;;   8. the dead declare-function forms in lisp/files.el and
;;;      lisp/menu-bar.el are gone;
;;;   9. src/deps.mk names no removed header (msdos.h, dosfns.h,
;;;      w32term.h).
;;;
;;; The repo root is bound by the .el wrapper as %m29-root (the harness
;;; loads the corpus with CWD=test/).
;;;
;;; The .el wrapper turns each (NAME STATUS) pair into an ERT test, so
;;; the harness counts the corpus; see test-m29-imp5.el.

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

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m29-root))
    (begin (report "m29-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m29-root ".")))

(define (repo path) (string-append %m29-root "/" path))

;;; --- 1. No dropped-platform token in src/keyboard.c -----------------
;;; FRAME_MSDOS_P is an inert frame macro (brief.org "What stays"), not
;;; an #ifdef arm, so it is stripped before the scan.
(define kbd-tokens '("MSDOS" "WINDOWSNT" "HAVE_NS" "HAIKU" "ANDROID"
                     "DOS_NT" "NTGUI"))

(let ((body (slurp (repo "src/keyboard.c"))))
  (if (not body)
      (report "kbd:present" (cons 'FAIL "src/keyboard.c missing"))
      (let* ((stripped (strip-all body "FRAME_MSDOS_P"))
             (hits (filter (lambda (tok) (has? stripped tok)) kbd-tokens)))
        (if (null? hits)
            (report "kbd:no-dropped-token" 'PASS)
            (report "kbd:no-dropped-token"
                    (cons 'FAIL (format #f "tokens ~s" hits)))))))

;;; --- 2. Config-variance arms survive -------------------------------
(define kept-arms
  '("USE_TOOLKIT_SCROLL_BARS" "HAVE_X_WINDOWS" "HAVE_TEXT_CONVERSION"))

(for-each
 (lambda (tok)
   (let ((body (slurp (repo "src/keyboard.c"))))
     (if (has? body tok)
         (report (string-append "kbd:kept-arm:" tok) 'PASS)
         (report (string-append "kbd:kept-arm:" tok)
                 (cons 'FAIL "config-variance arm gone (over-deleted)")))))
 kept-arms)

;;; --- 3. Deleted Lisp / etc paths are gone --------------------------
(define deleted-paths
  '("lisp/w32-vars.el" "lisp/w32-fns.el" "lisp/dos-w32.el"
    "lisp/term/w32console.el" "lisp/term/w32-win.el"
    "lisp/term/cygwin.el" "etc/w32-feature.el"))

(for-each
 (lambda (path)
   (let ((p (repo path)))
     (if (or (file-exists? p) (file-exists? (string-append p "/.")))
         (report (string-append "deleted:" path) (cons 'FAIL "still present"))
         (report (string-append "deleted:" path) 'PASS))))
 deleted-paths)

;;; --- 4. No live build file names a deleted path --------------------
(define deleted-name-tokens
  '("w32-vars" "w32-fns" "dos-w32" "w32console" "w32-win" "cygwin.el"
    "w32-feature"))

(define build-files
  '("lisp/loadup.el" "lisp/ldefs-boot.el" "lisp/Makefile.in"))

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

;;; lisp/loaddefs.el is generated and gitignored; the build regenerates
;;; it.  Check it only when the build has produced it.
(let ((body (slurp (repo "lisp/loaddefs.el"))))
  (if (not body)
      (report "no-deleted-name:lisp/loaddefs.el(absent)" 'PASS)
      (let ((hits (filter (lambda (tok) (has? body tok)) deleted-name-tokens)))
        (if (null? hits)
            (report "no-deleted-name:lisp/loaddefs.el" 'PASS)
            (report "no-deleted-name:lisp/loaddefs.el"
                    (cons 'FAIL (format #f "tokens ~s" hits)))))))

;;; --- 5. No over-deletion -------------------------------------------
(let ((cfg (slurp (repo "configure.ac"))))
  (if (has? cfg "AH_TEMPLATE([MSDOS]")
      (report "kept:AH_TEMPLATE-MSDOS" 'PASS)
      (report "kept:AH_TEMPLATE-MSDOS"
              (cons 'FAIL "AH_TEMPLATE([MSDOS]) gone (over-deleted)")))
  (if (and (has? cfg "cygwin)") (has? cfg "mingw32)"))
      (report "kept:opsys-cases" 'PASS)
      (report "kept:opsys-cases"
              (cons 'FAIL "opsys cygwin/mingw32 case gone (over-deleted)"))))

(let ((kbd (slurp (repo "src/keyboard.c"))))
  (if (has? kbd "FRAME_MSDOS_P")
      (report "kept:FRAME_MSDOS_P" 'PASS)
      (report "kept:FRAME_MSDOS_P"
              (cons 'FAIL "FRAME_MSDOS_P gone (over-deleted)"))))

;;; --- 6. Section 1.2 / 1.5 results of the keyboard.c sweep ----------
;;; The four dropped-platform DEFSYMs and the two dropped event-kind
;;; Fcons forms are gone, and the lispy_function_keys collapse yields
;;; the X keysym table at 0xff00 (brief.org 1.2 and 1.5).
(define kbd-body (slurp (repo "src/keyboard.c")))

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

;;; --- 7. loadup.el keeps the supported ns block ---------------------
(let ((body (slurp (repo "lisp/loadup.el"))))
  (if (has? body "term/ns-win")
      (report "kept:loadup-ns-block" 'PASS)
      (report "kept:loadup-ns-block"
              (cons 'FAIL "loadup.el ns block gone (over-deleted)"))))

;;; --- 8. Dead declare-function forms are gone -----------------------
(define (no-token? file token label)
  (let ((body (slurp (repo file))))
    (cond
     ((not body)
      (report (string-append label ":present") (cons 'FAIL "file missing")))
     ((has? body token)
      (report label (cons 'FAIL (format #f "~s still present" token))))
     (else (report label 'PASS)))))

(no-token? "lisp/files.el" "(declare-function w32-convert-standard-filename"
           "no-declare:w32-convert-standard-filename")
(no-token? "lisp/menu-bar.el" "(declare-function w32-menu-bar-open"
           "no-declare:w32-menu-bar-open")

;;; --- 9. src/deps.mk names no removed header (F4) -------------------
(let ((body (slurp (repo "src/deps.mk"))))
  (if (not body)
      (report "deps.mk-present" (cons 'FAIL "src/deps.mk missing"))
      (let ((hits (filter (lambda (tok) (has? body tok))
                          '("msdos.h" "dosfns.h" "w32term.h"))))
        (if (null? hits)
            (report "no-removed-header:src/deps.mk" 'PASS)
            (report "no-removed-header:src/deps.mk"
                    (cons 'FAIL (format #f "tokens ~s" hits)))))))

(reverse test-results)
