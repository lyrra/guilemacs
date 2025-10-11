;;; cus-dep.el --- find customization dependencies  -*- lexical-binding: t; -*-
;;
;; Copyright (C) 1997, 2001-2025 Free Software Foundation, Inc.
;;
;; Author: Per Abrahamsen <abraham@dina.kvl.dk>
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

;;; Code:

(require 'widget)
(require 'cus-face)
(require 'cl-lib)

(defvar generated-custom-dependencies-file "cus-load.el"
  "Output file for `custom-make-dependencies'.")

;; See finder-no-scan-regexp in finder.el.
(defvar custom-dependencies-no-scan-regexp "\\(^\\.#\\|\\(loaddefs\\|\
ldefs-boot\\|cus-load\\|finder-inf\\|esh-groups\\|subdirs\\)\\.el$\\)"
  "Regexp matching file names not to scan for `custom-make-dependencies'.")

(require 'loaddefs-gen)

;; Hack workaround for bug#14384.
;; Define defcustom-mh as an alias for defcustom, etc.
;; Only do this in batch mode to avoid messing up a normal Emacs session.
;; Alternative would be to load mh-e when making cus-load.
;; (Would be better to split just the necessary parts of mh-e into a
;; separate file and only load that.)
(when (and noninteractive)
  (mapc (lambda (e) (let ((sym (intern (format "%s-mh" e))))
		      (or (fboundp sym)
			  (defalias sym e))))
	'(defcustom defface defgroup))
  ;; FIX-guilemacs: Similar workaround for semantic's defcustom-mode-local-... macro
  ;; This macro expands to defcustom, so we can alias it to a wrapper that extracts
  ;; the defcustom part for cus-dep scanning.
  ;; The issue is that cus-dep.el's regex matches defcustom-mode-local-semantic-dependency-system-include-path because it starts with "defcustom". But this is a macro, not a
  ;; defcustom.
  ;; Use same workaround as above (where they create aliases for defcustom-mh, etc)
  (unless (fboundp 'defcustom-mode-local-semantic-dependency-system-include-path)
    (defmacro defcustom-mode-local-semantic-dependency-system-include-path
        (mode name value &optional docstring)
      "Simplified version for cus-dep scanning."
      `(defcustom ,name ,value
         ,(or docstring "")
         :group 'semantic
         :type '(repeat (directory :tag "Directory")))))
  ;; FIX-guilemacs: Workaround for erc's erc--with-dependent-type-match macro
  (unless (fboundp 'erc--with-dependent-type-match)
    (defmacro erc--with-dependent-type-match (type &rest _features)
      "Simplified version for cus-dep scanning - just return the type."
      `',type))
  ;; FIX-guilemacs: Workaround for todo-mode's todo--files-type-list function
  (unless (fboundp 'todo--files-type-list)
    (defun todo--files-type-list ()
      "Simplified version for cus-dep scanning - return empty list."
      nil))
  ;; FIX-guilemacs: Workaround for eshell's eshell-cmpl--custom-variable-docstring function
  (unless (fboundp 'eshell-cmpl--custom-variable-docstring)
    (defun eshell-cmpl--custom-variable-docstring (pcomplete-var)
      "Simplified version for cus-dep scanning - return placeholder docstring."
      (format "Eshell customization derived from `%s'." (symbol-name pcomplete-var))))
  ;; FIX-guilemacs: Workaround for eshell's eshell-subgroups function
  (unless (fboundp 'eshell-subgroups)
    (defun eshell-subgroups (groupsym)
      "Simplified version for cus-dep scanning - return empty list."
      nil))
  ;; FIX-guilemacs: Workaround for gnus's mm-coding-system-p function
  (unless (fboundp 'mm-coding-system-p)
    (defun mm-coding-system-p (coding-system)
      "Simplified version for cus-dep scanning - assume coding system exists."
      t))
  ;; FIX-guilemacs: Workaround for gnus's eieio-build-class-alist function
  (unless (fboundp 'eieio-build-class-alist)
    (defun eieio-build-class-alist (class &optional subclass)
      "Simplified version for cus-dep scanning - return empty list."
      nil))
  ;; FIX-guilemacs: Workaround for pakistan's pakistan--make-setter function
  (unless (fboundp 'pakistan--make-setter)
    (defun pakistan--make-setter (&optional prefix)
      "Simplified version for cus-dep scanning - return a simple setter."
      (lambda (var val) (set-default-toplevel-value var val))))
  ;; FIX-guilemacs: Workaround for mh-e's mh-variants function
  (unless (fboundp 'mh-variants)
    (defun mh-variants ()
      "Simplified version for cus-dep scanning - return empty list."
      nil))
  ;; FIX-guilemacs: Workaround for mh-e's mh-face-data function
  (unless (fboundp 'mh-face-data)
    (defun mh-face-data (face &optional inherit)
      "Simplified version for cus-dep scanning - return inherit or default spec."
      (or inherit '((t (:foreground "black"))))))
  ;; FIX-guilemacs: Workaround for cc-vars's defcustom-c-stylevar macro
  (unless (fboundp 'defcustom-c-stylevar)
    (defmacro defcustom-c-stylevar (name val doc &rest args)
      "Simplified version for cus-dep scanning."
      `(defcustom ,name ,val ,doc ,@args)))
  ;; FIX-guilemacs: Workaround for cc-vars's c-constant-symbol function
  (unless (fboundp 'c-constant-symbol)
    (defun c-constant-symbol (sym len)
      "Simplified version for cus-dep scanning."
      `(const :tag ,(symbol-name sym) ,sym)))
  ;; FIX-guilemacs: Workaround for cc-vars's c-make-font-lock-extra-types-blurb function
  (unless (fboundp 'c-make-font-lock-extra-types-blurb)
    (defun c-make-font-lock-extra-types-blurb (mode1 mode2 example)
      "Simplified version for cus-dep scanning."
      (format "List of extra types to recognize in %s mode." mode1))))

(defun custom--get-def (expr)
  (if (not (memq (car-safe expr)
                 '( define-minor-mode define-globalized-minor-mode)))
      expr
    ;; For define-minor-mode, we don't want to evaluate the whole
    ;; expression, because it tends to define functions which aren't
    ;; usable (because they call other functions that were skipped).
    ;; Concretely it gave us an error
    ;; "void-function bug-reference--run-auto-setup"
    ;; when subsequently loading `cus-load.el'.
    (let ((es (list (macroexpand-all expr)))
          defs)
      (while es
        (let ((e (pop es)))
          (pcase e
            (`(progn . ,exps) (setq es (append exps es)))
            (`(custom-declare-variable . ,_) (push e defs)))))
      (macroexp-progn (nreverse defs)))))

(defun custom-make-dependencies ()
  "Batch function to extract custom dependencies from .el files.
Usage: emacs -batch -l ./cus-dep.el -f custom-make-dependencies DIRS"
  (let* ((enable-local-eval nil)
	 (enable-local-variables :safe)
         (preloaded (concat "\\`\\(\\./+\\)?"
                            (regexp-opt preloaded-file-list t)
                            "\\.el\\'"))
         (file-count 0)
         (files
          ;; Use up command-line-args-left else Emacs can try to open
          ;; the args as directories after we are done.
          (cl-loop for subdir = (pop command-line-args-left)
                   while subdir
                   append (mapcar (lambda (f)
                                    (cons subdir f))
                                  (directory-files subdir nil
                                                   "\\`[^=.].*\\.el\\'"))))
	 (progress (make-progress-reporter
                    (byte-compile-info "Scanning files for custom")
                    0 (length files) nil 10)))
    (with-temp-buffer
      (dolist (elem files)
        (let* ((subdir (car elem))
               (file (cdr elem))
               (default-directory
                 (directory-file-name (expand-file-name subdir))))
          (progress-reporter-update progress (setq file-count (1+ file-count)))
          (unless (or (string-match custom-dependencies-no-scan-regexp file)
                      (string-match preloaded (format "%s/%s" subdir file))
                      (not (file-exists-p file)))
            (erase-buffer)
            (kill-all-local-variables)
            (insert-file-contents file)
            (hack-local-variables)
            (goto-char (point-min))
            (string-match "\\`\\(.*\\)\\.el\\'" file)
            (let ((name (or generated-autoload-load-name ; see bug#5277
                            (file-name-nondirectory (match-string 1 file))))
                  (load-true-file-name file)
                  (load-file-name file))
              (if (save-excursion
                    (re-search-forward
		     (concat "(\\(cc-\\)?provide[ \t\n]+\\('\\|(quote[ \t\n]\\)[ \t\n]*"
			     (regexp-quote name) "[ \t\n)]")
		     nil t))
                  (setq name (intern name)))
              (condition-case nil
                  (while (re-search-forward
                          "^(def\\(custom\\|face\\|group\\|ine\\(?:-globalized\\)?-minor-mode\\)" nil t)
                    (beginning-of-line)
                    (let ((type (match-string 1))
			  (expr (custom--get-def (read (current-buffer)))))
                      (condition-case err
                          (let ((custom-dont-initialize t)
                                (sym (nth 1 expr)))
                            (put (if (eq (car-safe sym) 'quote)
                                     (cadr sym)
                                   sym)
                                 'custom-where name)
                            ;; Eval to get the 'custom-group, -tag,
                            ;; -version, group-documentation etc properties.
                            (eval expr t))
                        ;; Eval failed for some reason.  Eg maybe the
                        ;; defcustom uses something defined earlier
                        ;; in the file (we haven't loaded the file).
                        ;; In most cases, we can still get the :group.
                        (error
                         ;; FIX-guilemacs: Add debugging output for errors
                         (message "Warning: Error in file %s, expr %S: %S" file (nth 1 expr) err)
                         (ignore-errors
                           (let ((group (cadr (memq :group expr))))
                             (and group
                                  (eq (car group) 'quote)
                                  (custom-add-to-group
                                   (cadr group)
                                   (nth 1 expr)
                                   (intern (format "custom-%s"
                                                   (if (equal type "custom")
                                                       "variable"
                                                     type)))))))))))
                (error nil)))))))
    (progress-reporter-done progress))
  (byte-compile-info
   (format "Generating %s..." generated-custom-dependencies-file) t)
  (set-buffer (find-file-noselect generated-custom-dependencies-file))
  (setq buffer-undo-list t)
  (erase-buffer)
  (generate-lisp-file-heading
   generated-custom-dependencies-file 'custom-make-dependencies
   :title "custom dependencies")
  (let (alist)
    (mapatoms (lambda (symbol)
		(let ((members (get symbol 'custom-group))
		      where found)
		  (when members
		    (dolist (member (mapcar #'car members))
		      (setq where (get member 'custom-where))
		      (unless (or (null where)
				  (member where found))
			(push where found)))
		    (when found
		      (push (cons (symbol-name symbol)
				  (with-output-to-string
				    (prin1 (sort found #'string<))))
			    alist))))))
    (dolist (e (sort alist (lambda (e1 e2) (string< (car e1) (car e2)))))
      (insert "(custom--add-custom-loads '" (car e) " '" (cdr e) ")\n")))
  (insert "\

;; The remainder of this file is for handling :version.
;; We provide a minimum of information so that `customize-changed'
;; can do its job.

;; For groups we set `custom-version', `group-documentation' and
;; `custom-tag' (which are shown in the customize buffer), so we
;; don't have to load the file containing the group.

;; This macro is used so we don't modify the information about
;; variables and groups if it's already set. (We don't know when
;; " (file-name-nondirectory generated-custom-dependencies-file)
      " is going to be loaded and at that time some of the
;; files might be loaded and some others might not).
\(defmacro custom-put-if-not (symbol propname value)
  `(unless (get ,symbol ,propname)
     (put ,symbol ,propname ,value)))

")
  (let ((version-alist nil)
	groups)
    (mapatoms (lambda (symbol)
		(let ((version (get symbol 'custom-version))
		      where)
		  (when version
		    (setq where (get symbol 'custom-where))
		    (when where
		      (if (or (custom-variable-p symbol)
                              (facep symbol))
			  ;; This means it's a variable or a face.
			  (progn
			    (if (assoc version version-alist)
				(unless
				    (member where
					    (cdr (assoc version version-alist)))
				  (push where (cdr (assoc version version-alist))))
			      (push (list version where) version-alist)))
			;; This is a group
			(push (list (symbol-name symbol)
				    (with-output-to-string (prin1 version))
				    (with-output-to-string
				      (prin1 (get symbol 'group-documentation)))
				    (if (get symbol 'custom-tag)
					(with-output-to-string
					  (prin1 (get symbol 'custom-tag)))))
			      groups)))))))
    (dolist (e (sort groups (lambda (e1 e2) (string< (car e1) (car e2)))))
      (insert "(custom-put-if-not '" (car e) " 'custom-version '"
	      (nth 1 e) ")\n")
      (insert "(custom-put-if-not '" (car e) " 'group-documentation "
	      (nth 2 e) ")\n")
      (if (nth 3 e)
	  (insert "(custom-put-if-not '" (car e) " 'custom-tag "
		  (nth 3 e) ")\n")))

    (insert "\n(defvar custom-versions-load-alist "
	    (if version-alist "'" ""))
    (prin1 (sort version-alist (lambda (e1 e2) (version< (car e1) (car e2))))
	   (current-buffer))
    (insert "\n  \"For internal use by custom.
This is an alist whose members have as car a version string, and as
elements the files that have variables or faces that contain that
version.  These files should be loaded before showing the customization
buffer that `customize-changed' generates.\")\n\n"))
  (generate-lisp-file-trailer generated-custom-dependencies-file)
  (save-buffer)
  (byte-compile-info
   (format "Generating %s...done" generated-custom-dependencies-file) t))


(provide 'cus-dep)

;;; cus-dep.el ends here
