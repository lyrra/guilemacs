;;; bookmark-tests.el --- Tests for bookmark.el  -*- lexical-binding: t -*-

;; Copyright (C) 2019-2025 Free Software Foundation, Inc.

;; Author: Stefan Kangas <stefankangas@gmail.com>

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

(require 'ert)
(require 'ert-x)
(require 'bookmark)
(require 'cl-lib)

(defvar bookmark-tests-bookmark-file (ert-resource-file "test.bmk")
  "Bookmark file used for testing.")

(defvar bookmark-tests-example-file
  ;; We use abbreviate-file-name here to match the behavior of
  ;; `bookmark-buffer-file-name'.
  (abbreviate-file-name (ert-resource-file "example.txt"))
  "Example file used for testing.")

;; The values below should match `bookmark-tests-bookmark-file'.  We cache
;; these values to speed up tests by avoiding unnecessary I/O.  This
;; makes tests run 5-10 times faster on my system.
(eval-and-compile  ; needed by `with-bookmark-test' macro
  (defvar bookmark-tests-bookmark '("name"
                            (filename . "/some/file")
                            (front-context-string . "abc")
                            (rear-context-string . "def")
                            (position . 3))
    "Cached value used in bookmark-tests.el."))

(defvar bookmark-tests-cache-timestamp
  (cons bookmark-tests-bookmark-file
        (nth 5 (file-attributes
                bookmark-tests-bookmark-file)))
  "Cached value used in bookmark-tests.el.")

(defmacro with-bookmark-test (&rest body)
  "Create environment for testing bookmark.el and evaluate BODY.
Ensure a clean environment for testing, and do not change user
data when running tests interactively."
  `(with-temp-buffer
     (let ((bookmark-alist (quote (,(copy-sequence bookmark-tests-bookmark))))
           (bookmark-default-file bookmark-tests-bookmark-file)
           (bookmark-bookmarks-timestamp bookmark-tests-cache-timestamp)
           bookmark-save-flag)
       ,@body)))

(defmacro with-bookmark-test-file (&rest body)
  "Create environment for testing bookmark.el and evaluate BODY.
Same as `with-bookmark-test' but also opens the resource file
example.txt in a buffer, which can be accessed by callers through
the lexically-bound variable `buffer'."
  `(let ((buffer (find-file-noselect bookmark-tests-example-file)))
     (unwind-protect
         (with-bookmark-test
          ,@body)
       (kill-buffer buffer))))

(defvar bookmark-tests-bookmark-file-list (ert-resource-file "test-list.bmk")
  "Bookmark file used for testing a list of bookmarks.")

;; The values below should match `bookmark-tests-bookmark-file-list'
;; content.  We cache these values to speed up tests.
(eval-and-compile  ; needed by `with-bookmark-test-list' macro
  (defvar bookmark-tests-bookmark-list-0 '("name-0"
                            (filename . "/some/file-0")
                            (front-context-string . "ghi")
                            (rear-context-string . "jkl")
                            (position . 4))
    "Cached value used in bookmark-tests.el."))

;; The values below should match `bookmark-tests-bookmark-file-list'
;; content.  We cache these values to speed up tests.
(eval-and-compile  ; needed by `with-bookmark-test-list' macro
  (defvar bookmark-tests-bookmark-list-1 '("name-1"
                            (filename . "/some/file-1")
                            (front-context-string . "mno")
                            (rear-context-string . "pqr")
                            (position . 5))
    "Cached value used in bookmark-tests.el."))

;; The values below should match `bookmark-tests-bookmark-file-list'
;; content.  We cache these values to speed up tests.
(eval-and-compile  ; needed by `with-bookmark-test-list' macro
  (defvar bookmark-tests-bookmark-list-2 '("name-2"
                            (filename . "/some/file-2")
                            (front-context-string . "stu")
                            (rear-context-string . "vwx")
                            (position . 6))
    "Cached value used in bookmark-tests.el."))

(defvar bookmark-tests-cache-timestamp-list
  (cons bookmark-tests-bookmark-file-list
        (nth 5 (file-attributes
                bookmark-tests-bookmark-file-list)))
  "Cached value used in bookmark-tests.el.")

(defmacro with-bookmark-test-list (&rest body)
  "Create environment for testing bookmark.el and evaluate BODY.
Ensure a clean environment for testing, and do not change user
data when running tests interactively."
  `(with-temp-buffer
     (let ((bookmark-alist (quote (,(copy-sequence bookmark-tests-bookmark-list-0)
                                   ,(copy-sequence bookmark-tests-bookmark-list-1)
                                   ,(copy-sequence bookmark-tests-bookmark-list-2))))
           (bookmark-default-file bookmark-tests-bookmark-file-list)
           (bookmark-bookmarks-timestamp bookmark-tests-cache-timestamp-list)
           bookmark-save-flag)
       ,@body)))

(defmacro with-bookmark-test-file-list (&rest body)
  "Create environment for testing bookmark.el and evaluate BODY.
Same as `with-bookmark-test-list' but also opens the resource file
example.txt in a buffer, which can be accessed by callers through
the lexically-bound variable `buffer'."
  `(let ((buffer (find-file-noselect bookmark-tests-example-file)))
     (unwind-protect
         (with-bookmark-test-list
          ,@body)
       (kill-buffer buffer))))

(ert-deftest bookmark-tests-all-names ()
  (with-bookmark-test
   (should (equal (bookmark-all-names) '("name")))))

(ert-deftest bookmark-tests-get-bookmark ()
  (with-bookmark-test
   (should (equal (bookmark-get-bookmark "name") bookmark-tests-bookmark))))

(ert-deftest bookmark-tests-get-bookmark-record ()
  (with-bookmark-test
   (should (equal (bookmark-get-bookmark-record "name") (cdr bookmark-tests-bookmark)))))

(ert-deftest bookmark-tests-all-names-list ()
  (with-bookmark-test-list
   (should (equal (bookmark-all-names) '("name-0"
                                         "name-1"
                                         "name-2")))))

(ert-deftest bookmark-tests-get-bookmark-list ()
  (with-bookmark-test-list
   (should (equal (bookmark-get-bookmark "name-0")
                  bookmark-tests-bookmark-list-0))
   (should (equal (bookmark-get-bookmark "name-1")
                  bookmark-tests-bookmark-list-1))
   (should (equal (bookmark-get-bookmark "name-2")
                  bookmark-tests-bookmark-list-2))))

(ert-deftest bookmark-tests-get-bookmark-record-list ()
  (with-bookmark-test-list
   (should (equal (bookmark-get-bookmark-record "name-0")
                  (cdr bookmark-tests-bookmark-list-0)))
   (should (equal (bookmark-get-bookmark-record "name-1")
                  (cdr bookmark-tests-bookmark-list-1)))
   (should (equal (bookmark-get-bookmark-record "name-2")
                  (cdr bookmark-tests-bookmark-list-2)))))

(ert-deftest bookmark-tests-record-getters-and-setters-new ()
  (with-temp-buffer
    (let* ((buffer-file-name "test")
           (bmk (bookmark-make-record)))
      (bookmark-set-name bmk "foobar")
      (should (equal (bookmark-name-from-full-record bmk) "foobar"))
      (bookmark-set-filename bmk "file/name")
      (should (equal (bookmark-get-filename bmk) "file/name"))
      (bookmark-set-position bmk 123)
      (should (equal (bookmark-get-position bmk) 123))
      (bookmark-set-front-context-string bmk "front")
      (should (equal (bookmark-get-front-context-string bmk) "front"))
      (bookmark-set-rear-context-string bmk "rear")
      (should (equal (bookmark-get-rear-context-string bmk) "rear"))
      (bookmark-prop-set bmk 'filename "prop")
      (should (equal (bookmark-prop-get bmk 'filename) "prop")))))

(ert-deftest bookmark-tests-maybe-historicize-string ()
  (let ((bookmark-history))
    (bookmark-maybe-historicize-string "foo")
    (should (equal (car bookmark-history) "foo"))))

(defun bookmark-remove-last-modified (bmk)
  (assoc-delete-all 'last-modified bmk))

(ert-deftest bookmark-tests-make-record ()
  (with-bookmark-test-file
   (let* ((record `("example.txt" (filename . ,bookmark-tests-example-file)
                    (front-context-string . "is text file is ")
                    (rear-context-string)
                    (position . 3)
                    (defaults "example.txt"))))
     (with-current-buffer buffer
       (goto-char 3)
       (should (equal (bookmark-remove-last-modified (bookmark-make-record))
                      record))
       ;; calling twice gives same record
       (should (equal (bookmark-remove-last-modified (bookmark-make-record))
                      record))))))

(ert-deftest bookmark-tests-make-record-list ()
  (with-bookmark-test-file-list
   (let* ((record `("example.txt" (filename . ,bookmark-tests-example-file)
                    (front-context-string . "is text file is ")
                    (rear-context-string)
                    (position . 3)
                    (defaults "example.txt"))))
     (with-current-buffer buffer
       (goto-char 3)
       (should (equal (bookmark-remove-last-modified (bookmark-make-record))
                      record))
       ;; calling twice gives same record
       (should (equal (bookmark-remove-last-modified (bookmark-make-record))
                      record))))))

(ert-deftest bookmark-tests-make-record-function ()
  (with-bookmark-test
   (let ((buffer-file-name "test"))
     ;; Named bookmark
     (let ((bookmark-make-record-function (lambda () '("<name>"))))
       (should (equal (bookmark-make-record)
                      '("<name>"))))
     ;; SECOND format
     (let ((bookmark-make-record-function (lambda () '(((position . 2))))))
       (should (equal (bookmark-make-record)
                      '("test" ((position . 2) (defaults "test"))))))
     ;; CURRENT format
     (let ((bookmark-make-record-function (lambda () '((position . 2)))))
       (should (equal (bookmark-make-record)
                      '("test" (position . 2) (defaults "test"))))))))

(ert-deftest bookmark-tests-set ()
  (with-bookmark-test-file
   (let ((bmk1 `("foo" (filename . ,bookmark-tests-example-file)
                 (front-context-string . "This text file i")
                 (rear-context-string)
                 (position . 1)))
         (bmk2 `("foo" (filename . ,bookmark-tests-example-file)
                 (front-context-string)
                 (rear-context-string . ".txt ends here.\n")
                 (position . 72)))
         bookmark-alist)
     (with-current-buffer buffer
       ;; 1. bookmark-set
       ;; Set first bookmark
       (goto-char (point-min))
       (bookmark-set "foo")
       (should (equal (mapcar #'bookmark-remove-last-modified bookmark-alist)
                      (list bmk1)))
       ;; Replace that bookmark
       (goto-char (point-max))
       (bookmark-set "foo")
       (should (equal (mapcar #'bookmark-remove-last-modified bookmark-alist)
                      (list bmk2)))
       ;; Push another bookmark with the same name
       (goto-char (point-min))
       (bookmark-set "foo" t)                   ; NO-OVERWRITE is t
       (should (equal (mapcar #'bookmark-remove-last-modified bookmark-alist)
                      (list bmk1 bmk2)))

       ;; 2. bookmark-set-no-overwrite
       ;; Don't overwrite
       (should-error (bookmark-set-no-overwrite "foo"))
       ;; Set new bookmark
       (setq bookmark-alist nil)
       (bookmark-set-no-overwrite "foo")
       (should (equal (mapcar #'bookmark-remove-last-modified bookmark-alist)
                      (list bmk1)))
       ;; Push another bookmark with the same name
       (goto-char (point-max))
       (bookmark-set-no-overwrite "foo" t)        ; PUSH-BOOKMARK is t
       (should (equal (mapcar #'bookmark-remove-last-modified bookmark-alist)
                      (list bmk2 bmk1)))

       ;; 3. bookmark-set-internal
       (should-error (bookmark-set-internal "foo" "bar" t))))))

'(DISABLE-guilemacs ert-deftest bookmark-tests-set/bookmark-use-annotations-t ()
  (with-bookmark-test-file
   (let ((bookmark-use-annotations t))
     (save-window-excursion
       (switch-to-buffer buffer)
       ;; Should jump to edit annotation buffer
       (bookmark-set "foo")
       (should (equal major-mode 'bookmark-edit-annotation-mode))
       ;; Should return to the original buffer
       (bookmark-edit-annotation-confirm)
       (should (equal (current-buffer) buffer))))))

(ert-deftest bookmark-tests-kill-line ()
  (with-temp-buffer
    (insert "foobar\n")
    (goto-char (point-min))
    (bookmark-kill-line)
    (should (equal (buffer-string) "\n")))
  (with-temp-buffer
    (insert "foobar\n")
    (goto-char (point-min))
    (bookmark-kill-line t)  ; including newline
    (should (equal (buffer-string) ""))))

(ert-deftest bookmark-tests-default-annotation-text ()
  (should (stringp (bookmark-default-annotation-text "foo")))
  (should (string-match "foo" (bookmark-default-annotation-text "foo"))))

(ert-deftest bookmark-tests-insert-annotation ()
  (with-bookmark-test
   (should-error (bookmark-insert-annotation "a missing bookmark"))
   (bookmark-insert-annotation "name")
   (should (string-match "Type the annotation" (buffer-string))))
  (with-bookmark-test
   (bookmark-set-annotation "name" "some stuff")
   (bookmark-insert-annotation "name")
   (should (string-match "some stuff" (buffer-string)))))

'(DISABLE-guilemacs ert-deftest bookmark-tests-edit-annotation ()
  (with-bookmark-test
   (bookmark-edit-annotation "name")
   (insert "new text")
   (bookmark-edit-annotation-confirm)
   (should (equal (bookmark-get-annotation "name") "new text"))))
