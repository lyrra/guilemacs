;;; loadup.el --- load up always-loaded Lisp files for Emacs  -*- lexical-binding: t; -*-

;; Copyright (C) 1985-1986, 1992, 1994, 2001-2025 Free Software
;; Foundation, Inc.

;; Maintainer: emacs-devel@gnu.org
;; Keywords: internal
;; Package: emacs

;; This file is part of GNU Emacs.

;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;; This is loaded into a bare Emacs to make a dumpable one.

;; Emacs injects the variable `dump-mode' to tell us how to dump.
;; We unintern it before allowing user code to run.

;; If you add a file to be loaded here, keep the following points in mind:

;; i) If the file is no-byte-compile, explicitly load the .el version.

;; ii) If the file is dumped with Emacs (on any platform), put the
;; load statement at the start of a line (leading whitespace is ok).

;; iii) If the file is _not_ dumped with Emacs, make sure the load
;; statement is _not_ at the start of a line.  See pcase for an example.

;; These rules are so that src/Makefile can construct lisp.mk
;; automatically.  This ensures that the Lisp files are compiled (if
;; necessary) before the "emacs" executable is dumped.

;;; Code:

;; This is used in xdisp.c to determine when bidi reordering is safe.
;; (It starts non-nil in temacs, but we set it non-nil here anyway, in
;; case someone loads loadup one more time.)  We reset it after
;; successfully loading charprop.el, which defines the Unicode tables
;; bidi.c needs for its job.
(setq redisplay--inhibit-bidi t)

(message "Dump mode: %s" dump-mode)

;; Add subdirectories to the load-path for files that might get
;; autoloaded when bootstrapping or running Emacs normally.
;; This is because PATH_DUMPLOADSEARCH is just "../lisp".
(if (or (member dump-mode '("bootstrap" "pbootstrap"))
	;; FIXME this is irritatingly fragile.
        (and (stringp (nth 4 command-line-args))
             (string-match "^unidata-gen\\(\\.elc?\\)?$"
                           (nth 4 command-line-args)))
        (member (nth 7 command-line-args) '("unidata-gen-file"
                                            "unidata-gen-charprop"))
        (null dump-mode))
    (progn
      ;; Find the entry in load-path that contains Emacs elisp and
      ;; splice some additional directories in there for the benefit
      ;; of autoload and regular Emacs use.
      (let ((subdirs '("emacs-lisp"
                       "progmodes"
                       "language"
                       "international"
                       "textmodes"
                       "vc"))
            (iter load-path))
        (while iter
          (let ((dir (car iter))
                (subdirs subdirs)
                esubdirs esubdir)
            (while subdirs
              (setq esubdir (expand-file-name (car subdirs) dir))
              (setq subdirs (cdr subdirs))
              (if (file-directory-p esubdir)
                  (setq esubdirs (cons esubdir esubdirs))
                (setq subdirs nil esubdirs nil)))
            (if esubdirs
                (progn
                  (setcdr iter (nconc (nreverse esubdirs) (cdr iter)))
                  (setq iter nil))
              (setq iter (cdr iter))
              (if (null iter)
                  (signal
                   'error (list
                           (format-message
                            "Could not find elisp load-path: searched %S"
                            load-path))))))))
      ;; We'll probably overflow the pure space.
      (setq purify-flag nil)
      ;; Value of max-lisp-eval-depth when compiling initially.
      ;; During bootstrapping the byte-compiler is run interpreted
      ;; when compiling itself, which uses a lot more stack
      ;; than usual.
      (setq max-lisp-eval-depth (max max-lisp-eval-depth 3400))))

(message "Using load-path %s" load-path)

(if dump-mode
    (progn
      ;; To reduce the size of dumped Emacs, we avoid making huge char-tables.
      (setq inhibit-load-charset-map t)
      ;; --eval gets handled too late.
      (defvar load--prefer-newer load-prefer-newer)
      (setq load-prefer-newer t)))

;; We don't want to have any undo records in the dumped Emacs.
(set-buffer "*scratch*")
(setq buffer-undo-list t)

(load "emacs-lisp/debug-early")
(load "emacs-lisp/byte-run")
(load "emacs-lisp/backquote")
(load "subr")

;; Load-time macro-expansion can only take effect after setting
;; load-source-file-function because of where it is called in lread.c.
(load "emacs-lisp/macroexp")
(if (compiled-function-p (symbol-function 'macroexpand-all))
    nil
  ;; Since loaddefs is not yet loaded, macroexp's uses of pcase will simply
  ;; fail until pcase is explicitly loaded.  This also means that we have to
  ;; disable eager macro-expansion while loading pcase.
  (let ((macroexp--pending-eager-loads '(skip))) (load "emacs-lisp/pcase"))
  ;; Re-load macroexp so as to eagerly macro-expand its uses of pcase.
  (let ((max-lisp-eval-depth (* 2 max-lisp-eval-depth)))
    (load "emacs-lisp/macroexp")))

(load "keymap")


(load "international/mule")
(load "international/mule-conf")
; Following is moved out from mule-conf:
(defcustom password-word-equivalents
  '("password" "passcode" "passphrase" "pass phrase" "pin"
    "decryption key" "encryption key" ; From ccrypt.
    )
  "List of words equivalent to \"password\".
This is used by Shell mode and other parts of Emacs to recognize
password prompts, including prompts in languages other than
English.  Different case choices should not be assumed to be
included; callers should bind `case-fold-search' to t."
  :type '(repeat string)
  :version "27.1"
  :group 'processes)
(defcustom password-colon-equivalents
  '(?\u003a ; ?\N{COLON}
    ?\uff1a ; ?\N{FULLWIDTH COLON}
    ?\ufe55 ; ?\N{SMALL COLON}
    ?\ufe13 ; ?\N{PRESENTATION FORM FOR VERTICAL COLON}
    ?\u17d6 ; ?\N{KHMER SIGN CAMNUC PII KUUH}
    )
  "List of characters equivalent to trailing colon in \"password\" prompts."
  :type '(repeat character)
  :version "30.1"
  :group 'processes)

;; Do it after subr, since both after-load-functions and add-hook are
;; implemented in subr.el.
(add-hook 'after-load-functions (lambda (_) (garbage-collect)))

(load "version")

(load "widget")
(load "custom")

(defcustom search-slow-speed 1200
  "Highest terminal speed at which to use \"slow\" style incremental search.
This is the style where a one-line window is created to show the line
that the search has reached."
  :type 'integer)

(load "emacs-lisp/map-ynp")
(load "env")
(load "format")
(load "bindings")

(load "buffer-match")
(load "window")  ; Needed here for `replace-buffer-in-windows'.
;; We are now capable of resizing the mini-windows, so give the
;; variable its advertised default value (it starts as nil, see
;; xdisp.c).
(setq resize-mini-windows 'grow-only)
; FIX-guilemacs: disabled, why?
;(setq load-source-file-function #'load-with-code-conversion)
(load "files")

(load "emacs-lisp/gv")

(load "cus-face")
(load "faces")  ; after here, `defface' may be used.


(load "subr2")

;; We don't want to store loaddefs.el in the repository because it is
;; a generated file; but it is required in order to compile the lisp files.
;; When bootstrapping, we cannot generate loaddefs.el until an
;; emacs binary has been built.  We therefore compromise and keep
;; ldefs-boot.el in the repository.  This does not need to be updated
;; as often as the real loaddefs.el would.  Bootstrap should always
;; work with ldefs-boot.el.  Therefore, whenever a new autoload cookie
;; gets added that is necessary during bootstrapping, ldefs-boot.el
;; should be updated by overwriting it with an up-to-date copy of
;; loaddefs.el that is not corrupted by local changes.
;; admin/update_autogen can be used to update ldefs-boot.el periodically.
;(condition-case nil
;    (load "loaddefs")
;  (file-error
;   (load "ldefs-boot.el")))
(load "ldefs-boot.el") ; guilemacs, disable loading of loaddefs for now


(let ((new (make-hash-table :test #'equal)))
  ;; Now that loaddefs has populated definition-prefixes, purify its contents.
  (maphash (lambda (k v) (puthash (purecopy k) (purecopy v) new))
           definition-prefixes)
  (setq definition-prefixes new))

(load "button")                  ;After loaddefs, because of define-minor-mode!

(when (interpreted-function-p (symbol-function 'add-hook))
  ;; `subr.el' is needed early and hence can't use macros like `setf'
  ;; liberally.  Yet, it does use such macros in code that it knows will not
  ;; be executed too early, such as `add-hook'.  Usually, by the time we
  ;; run that code, either `subr.el' was already compiled to start with
  ;; or on the contrary many files aren't compiled yet and have thus caused
  ;; macro packages like `gv' to be loaded.  But not always.
  ;; The specific error we're trying to work around, here, occurs when
  ;; `cl-preloaded's `provide' ends up (because of an `eval-after-load')
  ;; calling `add-hook' which burps with a "void-function setf" on
  ;; (setf (get hook 'hook--depth-alist) depth-sym)'.
  ;; FIXME: We should probably split `subr.el' into one that's loaded early
  ;; where we refrain from using macros like `setf', and another loaded later
  ;; where we can blissfully `require' packages like `gv'.
  (require 'gv))

(load "emacs-lisp/cl-preloaded")
(load "emacs-lisp/oclosure")          ;Used by cl-generic
(load "emacs-lisp/derived")
(load "emacs-lisp/easy-mmode")
(load "obarray")        ;abbrev.el is implemented in terms of obarrays.
(load "abbrev")         ;lisp-mode.el and simple.el use define-abbrev-table.

(load "emacs-lisp/cl-lib")
(load "emacs-lisp/cl-macs")

(load "help-macro")
(load "help")
(load "emacs-lisp/cl-generic")
(load "simple")
(load "help-fns")

(load "faces2")

(load "jka-cmpr-hook")
(load "epa-hook")
;; Any Emacs Lisp source file (*.el) loaded here after can contain
;; multilingual text.
(load "international/mule-cmds")
(load "case-table")
;; This file doesn't exist when building a development version of Emacs
;; from the repository.  It is generated just after temacs is built.
(load "international/charprop.el" t)
(if (featurep 'charprop)
    (setq redisplay--inhibit-bidi nil))
(load "international/characters")
(load "composite")

(load "international/ccl")

;; FIX-guilemacs: not sure why disabled
;; Load language-specific files.
;(load "language/chinese")
;(load "language/cyrillic")
;(load "language/indian")
;(load "language/sinhala")
(load "language/english")
;(load "language/ethiopic")
;(load "language/european")
;(load "language/czech")
;(load "language/slovak")
;(load "language/romanian")
;(load "language/greek")
;(load "language/hebrew")
;(load "international/cp51932")
;(load "international/eucjp-ms")
;(load "language/japanese")
;(load "language/korean")
;(load "language/lao")
;(load "language/tai-viet")
;(load "language/thai")
;(load "language/tibetan")
;(load "language/vietnamese")
(load "language/misc-lang")
(load "language/utf-8-lang")
;(load "language/georgian")
;(load "language/khmer")
;(load "language/burmese")
;(load "language/cham")
;(load "language/philippine")
;(load "language/indonesian")

(load "indent")
(load "minibuffer") ; Needs cl-generic, seq (and define-minor-mode).
(load "emacs-lisp/seq")
(load "emacs-lisp/nadvice")
(load "minibuffer") ;Needs cl-generic (and define-minor-mode).
(load "frame")
(load "startup")
(load "term/tty-colors")
(load "font-core")
(load "emacs-lisp/syntax")
(load "font-lock")
(load "jit-lock")

(load "mouse")
;; This loading happens on Android despite scroll bars being
;; unsupported, because scroll-bar-mode (the variable) must be
;; defined.
(if (boundp 'x-toolkit-scroll-bars)
    (load "scroll-bar"))
(load "select")
(load "emacs-lisp/timer")
(load "emacs-lisp/easymenu")
(load "isearch")
(load "rfn-eshadow")

(load "menu-bar")
(load "tab-bar")
(load "emacs-lisp/lisp")
(load "textmodes/page")
(load "register")
(load "textmodes/paragraphs")
(load "progmodes/prog-mode")
(load "emacs-lisp/lisp-mode")
(load "textmodes/text-mode")
(load "textmodes/fill")
(load "newcomment")

(load "replace")
(load "emacs-lisp/tabulated-list")
(load "kmacro")
(load "buff-menu")

(if (fboundp 'x-create-frame)
    (progn
      (load "fringe")
      ;; Needed by `imagemagick-register-types'
      (load "emacs-lisp/regexp-opt")
      (load "image")
      (load "international/fontset")
      (load "dnd")
      (load "tool-bar")))

(if (featurep 'dynamic-setting)
    (load "dynamic-setting"))

(if (featurep 'x)
    (progn
      (load "touch-screen")
      (load "x-dnd")
      (load "term/common-win")
      (load "term/x-win")))

(if (featurep 'haiku)
    (progn
      (load "term/common-win")
      (load "term/haiku-win")))

(if (featurep 'android)
    (progn
      (load "ls-lisp")
      (load "touch-screen")
      (load "term/common-win")
      (load "term/android-win")))

(if (or (eq system-type 'windows-nt)
        (featurep 'w32))
    (progn
      (load "term/common-win")
      (load "w32-vars")
      (load "term/w32-win")
      (load "disp-table")
      (when (eq system-type 'windows-nt)
        (load "w32-fns")
        (load "ls-lisp")
        (load "dos-w32"))
      (load "touch-screen")))
(if (eq system-type 'ms-dos)
    (progn
      (load "dos-w32")
      (load "dos-fns")
      (load "dos-vars")
      ;; Don't load term/common-win: it isn't appropriate for the `pc'
      ;; ``window system'', which generally behaves like a terminal.
      (load "term/internal")
      (load "term/pc-win")
      (load "ls-lisp")
      (load "disp-table"))) ; needed to setup ibm-pc char set, see internal.el
(if (featurep 'ns)
    (progn
      (load "term/common-win")
      ;; Don't load ucs-normalize.el unless uni-*.el files were
      ;; already produced, because it needs uni-*.el files that might
      ;; not be built early enough during bootstrap.
      (when (featurep 'charprop)
        (load "international/mule-util")
        (load "international/ucs-normalize")
        (load "term/ns-win"))))
(if (featurep 'pgtk)
    (progn
      (load "pgtk-dnd")
      (load "touch-screen")
      (load "term/common-win")
      (load "term/pgtk-win")))
(if (fboundp 'x-create-frame)
    ;; Do it after loading term/foo-win.el since the value of the
    ;; mouse-wheel-*-event vars depends on those files being loaded or not.
    (load "mwheel"))

;; progmodes/elisp-mode.el must be after w32-fns.el, to avoid this:
;;"Eager macro-expansion failure: (void-function w32-convert-standard-filename)"
;; which happens while processing 'elisp-flymake-byte-compile', when
;; elisp-mode.elc is outdated.
(load "progmodes/elisp-mode")

;; Preload some constants and floating point functions.
(load "emacs-lisp/float-sup")

(load "vc/vc-hooks")
(load "vc/ediff-hook")
(load "uniquify")
(load "electric")
(load "paren")

(load "emacs-lisp/shorthands")

;(load "emacs-lisp/eldoc")
(load "emacs-lisp/cconv")
(when (and (compiled-function-p (symbol-function 'cconv-fv))
           (compiled-function-p (symbol-function 'macroexpand-all)))
  (setq internal-make-interpreted-closure-function
        #'cconv-make-interpreted-closure))
(load "cus-start") ;Late to reduce customize-rogue (needs loaddefs.el anyway)
(if (not (eq system-type 'ms-dos))
    (load "tooltip"))
(load "international/iso-transl") ; Binds Alt-[ and friends.

;; Used by `kill-buffer', for instance.
(load "emacs-lisp/rmc")

;; This file doesn't exist when building a development version of Emacs
;; from the repository.  It is generated just after temacs is built.
;(load "leim/leim-list.el" t)

;; If you want additional libraries to be preloaded and their
;; doc strings kept in the DOC file rather than in core,
;; you may load them with a "site-load.el" file.
;; But you must also cause them to be scanned when the DOC file
;; is generated.
(let ((lp load-path))
  (load "site-load" t)
  ;; We reset load-path after dumping.
  ;; For a permanent change in load-path, use configure's
  ;; --enable-locallisppath option.
  ;; See https://debbugs.gnu.org/16107 for more details.
  (or (equal lp load-path)
      (message "Warning: Change in load-path due to site-load will be \
lost after dumping")))

;; Actively check for advised functions during preload since:
;; - advices in Emacs's core are generally considered bad style;
;; - `Snarf-documentation' looses docstrings of primitives advised
;;   during preload (bug#66032#20).
'(mapatoms
 (lambda (f)
   (and (advice--p (symbol-function f))
        ;; Don't make it an error because it's not serious enough and
        ;; it can be annoying during development.  Also there are still
        ;; circumstances where we use advice on preloaded functions.
        (message "Warning: Advice installed on preloaded function %S" f))))

;; Make sure default-directory is unibyte when dumping.  This is
;; because we cannot decode and encode it correctly (since the locale
;; environment is not, and should not be, set up).  default-directory
;; is used every time we call expand-file-name, which we do in every
;; file primitive.  So the only workable solution to support building
;; in non-ASCII directories is to manipulate unibyte strings in the
;; current locale's encoding.
(if (and dump-mode (multibyte-string-p default-directory))
    (error "default-directory must be unibyte when dumping Emacs!"))

;; Determine which build number to use
;; based on the executables that now exist.
(if (and (or
          (and (equal dump-mode "dump")
               (fboundp 'dump-emacs))
          (and (equal dump-mode "pdump")
               (fboundp 'dump-emacs-portable)))
	 (not (eq system-type 'ms-dos)))
    (let* ((base (concat "emacs-" emacs-version "."))
	   (exelen (if (eq system-type 'windows-nt) -4))
	   (files (file-name-all-completions base default-directory))
	   (versions (mapcar (lambda (name)
                               (string-to-number
                                (substring name (length base) exelen)))
			     files)))
      (setq emacs-repository-version (ignore-errors (emacs-repository-get-version))
            emacs-repository-branch (ignore-errors (emacs-repository-get-branch)))
      ;; A constant, so we shouldn't change it with `setq'.
      (defconst emacs-build-number
	(if versions (1+ (apply #'max versions)) 1))))

;; Just set the repository branch during initial dumping on Android.
(if (eq system-type 'android)
    (setq emacs-repository-version
          (ignore-errors (emacs-repository-get-version))
          emacs-repository-branch
          (ignore-errors (emacs-repository-get-branch))))

(message "Finding pointers to doc strings...")
(if (and (or (and (fboundp 'dump-emacs)
                  (equal dump-mode "dump"))
             (and (fboundp 'dump-emacs-portable)
                  (equal dump-mode "pdump"))))
    (Snarf-documentation "DOC")
  (condition-case nil
      (Snarf-documentation "DOC")
    (error nil)))
(message "Finding pointers to doc strings...done")

;; Note: You can cause additional libraries to be preloaded
;; by writing a site-init.el that loads them.
;; See also "site-load" above
(let ((lp load-path))
  (load "site-init" t)
  (or (equal lp load-path)
      (message "Warning: Change in load-path due to site-init will be \
lost after dumping")))

;; Avoid storing references to build directory in the binary.
(setq custom-current-group-alist nil)

;; We keep the load-history data in PURE space.
;; Make sure that the spine of the list is not in pure space because it can
;; be destructively mutated in lread.c:build_load_history.
(setq load-history (mapcar #'purecopy load-history))

(set-buffer-modified-p nil)

(remove-hook 'after-load-functions (lambda (_) (garbage-collect)))

(if (boundp 'load--prefer-newer)
    (progn
      (setq load-prefer-newer load--prefer-newer)
      (put 'load-prefer-newer 'standard-value load--prefer-newer)
      (makunbound 'load--prefer-newer)))

(setq inhibit-load-charset-map nil)
(clear-charset-maps)
(garbage-collect)

;; At this point, we're ready to resume undo recording for scratch.
(buffer-enable-undo "*scratch*")

(defvar load--bin-dest-dir nil
  "Store the original value passed by \"--bin-dest\" during dump.
Internal use only.")
(defvar load--eln-dest-dir nil
  "Store the original value passed by \"--eln-dest\" during dump.
Internal use only.")

(when (hash-table-p purify-flag)
  (let ((strings 0)
        (vectors 0)
        (bytecodes 0)
        (conses 0)
        (others 0))
    (maphash (lambda (k v)
               (cond
                ((stringp k) (setq strings (1+ strings)))
                ((vectorp k) (setq vectors (1+ vectors)))
                ((consp k)   (setq conses  (1+ conses)))
                ((byte-code-function-p v) (setq bytecodes (1+ bytecodes)))
                (t           (setq others  (1+ others)))))
             purify-flag)
    (message "Pure-hashed: %d strings, %d vectors, %d conses, %d bytecodes, %d others"
             strings vectors conses bytecodes others)))

;; Avoid error if user loads some more libraries now and make sure the
;; hash-consing hash table is GC'd.
(setq purify-flag nil)

(if (null (garbage-collect))
    (setq pure-space-overflow t))

;; Make sure we will attempt bidi reordering henceforth.
(setq redisplay--inhibit-bidi nil)

;; This file must be loaded each time Emacs is run from scratch, e.g., temacs.
;; So run the startup code now.  First, remove `-l loadup' from args.

(if (and (member (nth 1 command-line-args) '("-l" "--load"))
	 (equal (nth 2 command-line-args) "loadup"))
    (setcdr command-line-args (nthcdr 3 command-line-args)))

;; Don't keep `load-file-name' set during the top-level session!
;; Otherwise, it breaks a lot of code which does things like
;; (or load-file-name byte-compile-current-file).
(setq load-true-file-name nil)
(setq load-file-name nil)
(eval top-level t)

;; loadup.el is loaded at startup, but clobbers current-load-list.
;; Set current-load-list to a list containing no definitions and only
;; its name, to prevent invalid entries from ending up in
;; Vload_history when running temacs interactively.

(setq current-load-list (list "loadup.el"))


;; Local Variables:
;; no-byte-compile: t
;; no-update-autoloads: t
;; End:

;;; loadup.el ends here
