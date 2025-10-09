;;; shortdoc.el --- Short function summaries  -*- lexical-binding: t -*-

;; Copyright (C) 2020-2025 Free Software Foundation, Inc.

;; Keywords: lisp, help
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

;; This package lists functions based on various groupings.
;;
;; For instance, `string-trim' and `mapconcat' are `string' functions,
;; so `M-x shortdoc RET string RET' will give an overview of functions
;; that operate on strings.
;;
;; The documentation groups are created with the
;; `define-short-documentation-group' macro.

;;; Code:

(require 'seq)
(require 'text-property-search)
(eval-when-compile (require 'cl-lib))

(defgroup shortdoc nil
  "Short documentation."
  :group 'lisp)

(defface shortdoc-heading
  '((t :inherit variable-pitch :height 1.3 :weight bold))
  "Face used for a heading."
  :version "28.1")

(defface shortdoc-section
  '((t :inherit variable-pitch))
  "Face used for a section.")

;;;###autoload
(defun shortdoc--check (group functions)
  (let ((keywords '( :no-manual :args :eval :no-eval :no-value :no-eval*
                     :result :result-string :eg-result :eg-result-string :doc)))
    (dolist (f functions)
      (when (consp f)
        (dolist (x f)
          (when (and (keywordp x) (not (memq x keywords)))
            (error "Shortdoc %s function `%s': bad keyword `%s'"
                   group (car f) x)))))))

;;;###autoload
(progn
  (defvar shortdoc--groups nil)

  (defmacro define-short-documentation-group (group &rest functions)
    "Add GROUP to the list of defined documentation groups.
FUNCTIONS is a list of elements on the form:

  (FUNC
   :no-manual BOOL
   :args ARGS
   :eval EVAL
   :no-eval EXAMPLE-FORM
   :no-value EXAMPLE-FORM
   :no-eval* EXAMPLE-FORM
   :result RESULT-FORM
   :result-string RESULT-STRING
   :eg-result RESULT-FORM
   :eg-result-string RESULT-STRING)

FUNC is the function being documented.

NO-MANUAL should be non-nil if FUNC isn't documented in the
manual.

ARGS is optional list of function FUNC's arguments.  FUNC's
signature is displayed automatically if ARGS is not present.
Specifying ARGS might be useful where you don't want to document
some of the uncommon arguments a function might have.

While the `:no-manual' and `:args' property can be used for
any (FUNC ..) form, all of the other properties shown above
cannot be used simultaneously in such a form.

Here are some common forms with examples of properties that go
together:

1. Document a form or string, and its evaluated return value.
   (FUNC
    :eval EVAL)

If EVAL is a string, it will be inserted as is, and then that
string will be `read' and evaluated.

2. Document a form or string, but manually document its evaluation
   result.  The provided form will not be evaluated.

  (FUNC
   :no-eval EXAMPLE-FORM
   :result RESULT-FORM)   ;Use `:result-string' if value is in string form

Using `:no-value' is the same as using `:no-eval'.

Use `:no-eval*' instead of `:no-eval' where the successful
execution of the documented form depends on some conditions.

3. Document a form or string EXAMPLE-FORM.  Also manually
   document an example result.  This result could be unrelated to
   the documented form.

  (FUNC
   :no-eval EXAMPLE-FORM
   :eg-result RESULT-FORM) ;Use `:eg-result-string' if value is in string form

A FUNC form can have any number of `:no-eval' (or `:no-value'),
`:no-eval*', `:result', `:result-string', `:eg-result' and
`:eg-result-string' properties."
    (declare (indent defun))
    (shortdoc--check group functions)
    `(progn
       (setq shortdoc--groups (delq (assq ',group shortdoc--groups)
                                    shortdoc--groups))
       (push (cons ',group ',functions) shortdoc--groups))))

(provide 'shortdoc)
