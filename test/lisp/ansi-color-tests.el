;;; ansi-color-tests.el --- Test suite for ansi-color  -*- lexical-binding: t; -*-

;; Copyright (C) 2020-2025 Free Software Foundation, Inc.

;; Author: Pablo Barbáchano <pablob@amazon.com>

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

(require 'ansi-color)
(eval-when-compile (require 'cl-lib))

(defvar ansi-color-tests--strings
  (let ((bright-yellow (face-foreground 'ansi-color-bright-yellow nil 'default))
        (yellow (face-foreground 'ansi-color-yellow nil 'default))
        (custom-color "#87FFFF"))
    `(("Hello World" "Hello World")
      ("\x1b[33mHello World\x1b[0m" "Hello World"
       (:foreground ,yellow))
      ("\x1b[43mHello World\x1b[0m" "Hello World"
       (:background ,yellow))
      ("\x1b[93mHello World\x1b[0m" "Hello World"
       (:foreground ,bright-yellow))
      ("\x1b[103mHello World\x1b[0m" "Hello World"
       (:background ,bright-yellow))
      ("\x1b[1;33mHello World\x1b[0m" "Hello World"
       (ansi-color-bold (:foreground ,yellow))
       (ansi-color-bold (:foreground ,bright-yellow)))
      ("\x1b[33;1mHello World\x1b[0m" "Hello World"
       (ansi-color-bold (:foreground ,yellow))
       (ansi-color-bold (:foreground ,bright-yellow)))
      ("\x1b[1m\x1b[33mHello World\x1b[0m" "Hello World"
       (ansi-color-bold (:foreground ,yellow))
       (ansi-color-bold (:foreground ,bright-yellow)))
      ("\x1b[33m\x1b[1mHello World\x1b[0m" "Hello World"
       (ansi-color-bold (:foreground ,yellow))
       (ansi-color-bold (:foreground ,bright-yellow)))
      ("\x1b[1m\x1b[3m\x1b[5mbold italics blink\x1b[0m" "bold italics blink"
       (ansi-color-bold ansi-color-italic ansi-color-slow-blink))
      ("\x1b[10munrecognized\x1b[0m" "unrecognized")
      ("\x1b[38;5;3;1mHello World\x1b[0m" "Hello World"
       (ansi-color-bold (:foreground ,yellow))
       (ansi-color-bold (:foreground ,bright-yellow)))
      ("\x1b[48;5;123;1mHello World\x1b[0m" "Hello World"
       (ansi-color-bold (:background ,custom-color)))
      ("\x1b[48;2;135;255;255;1mHello World\x1b[0m" "Hello World"
       (ansi-color-bold (:background ,custom-color))))))

(defun ansi-color-tests-equal-props (o1 o2)
  "Return t if two Lisp objects have similar structure and contents.
While `equal-including-properties' compares text properties of
strings with `eq', this function compares them with `equal'."
  (or (equal-including-properties o1 o2)
      (and (stringp o1)
           (equal o1 o2)
           (cl-loop for i below (length o1)
                    always (equal (text-properties-at i o1)
                                  (text-properties-at i o2))))))

(ert-deftest ansi-color-apply-on-region-test ()
  (pcase-dolist (`(,input ,text ,face) ansi-color-tests--strings)
    (with-temp-buffer
      (insert input)
      (ansi-color-apply-on-region (point-min) (point-max))
      (should (equal (buffer-string) text))
      (should (equal (get-char-property (point-min) 'face) face))
      (when face
        (should (overlays-at (point-min)))))))

(ert-deftest ansi-color-apply-on-region-bold-is-bright-test ()
  (pcase-dolist (`(,input ,text ,normal-face ,bright-face)
                 ansi-color-tests--strings)
    (with-temp-buffer
      (let ((ansi-color-bold-is-bright t)
            (face (or bright-face normal-face)))
        (insert input)
        (ansi-color-apply-on-region (point-min) (point-max))
        (should (equal (buffer-string) text))
        (should (equal (get-char-property (point-min) 'face) face))
        (when face
          (should (overlays-at (point-min))))))))

(ert-deftest ansi-color-apply-on-region-preserving-test ()
  (dolist (pair ansi-color-tests--strings)
    (with-temp-buffer
      (insert (car pair))
      (ansi-color-apply-on-region (point-min) (point-max) t)
      (should (equal (buffer-string) (car pair))))))

(ert-deftest ansi-color-incomplete-sequences-test ()
  (let* ((strs (list "\x1b[" "2;31m Hello World "
                     "\x1b" "[108;5;12" "3m" "Greetings"
                     "\x1b[0m\x1b[35;6m" "Hello"))
         (complete-str (apply #'concat strs))
         (filtered-str)
         (propertized-str)
         (ansi-color-apply-face-function
          #'ansi-color-apply-text-property-face)
         (ansi-filt (lambda (str) (ansi-color-filter-apply
                                   (copy-sequence str))))
         (ansi-app (lambda (str) (ansi-color-apply
                                  (copy-sequence str)))))

    (with-temp-buffer
      (setq filtered-str
            (replace-regexp-in-string "\x1b\\[.*?m" "" complete-str))
      (setq propertized-str (funcall ansi-app complete-str))

      (should-not (ansi-color-tests-equal-props
                   filtered-str propertized-str))
      (should (equal filtered-str propertized-str)))

    ;; Tests for `ansi-color-filter-apply'
    (with-temp-buffer
      (should (equal-including-properties
               filtered-str
               (funcall ansi-filt complete-str))))

    (with-temp-buffer
      (should (equal-including-properties
               filtered-str
               (mapconcat ansi-filt strs))))

    ;; Tests for `ansi-color-filter-region'
    (with-temp-buffer
      (insert complete-str)
      (ansi-color-filter-region (point-min) (point-max))
      (should (equal-including-properties
               filtered-str (buffer-string))))

    (with-temp-buffer
      (dolist (str strs)
        (let ((opoint (point)))
          (insert str)
          (ansi-color-filter-region opoint (point))))
      (should (equal-including-properties
               filtered-str (buffer-string))))

    ;; Test for `ansi-color-apply'
    (with-temp-buffer
      (should (ansi-color-tests-equal-props
               propertized-str
               (mapconcat ansi-app strs))))

    ;; Tests for `ansi-color-apply-on-region'
    (with-temp-buffer
      (insert complete-str)
      (ansi-color-apply-on-region (point-min) (point-max))
      (should (ansi-color-tests-equal-props
               propertized-str (buffer-string))))

    (with-temp-buffer
      (dolist (str strs)
        (let ((opoint (point)))
          (insert str)
          (ansi-color-apply-on-region opoint (point))))
      (should (ansi-color-tests-equal-props
               propertized-str (buffer-string))))

    ;; \x1b not followed by '[' and invalid ANSI escape sequences
    (dolist (fun (list ansi-filt ansi-app))
      (with-temp-buffer
        (should (equal (funcall fun "\x1b") ""))
        (should (equal (funcall fun "\x1b[33m test \x1b[0m")
                       (with-temp-buffer
                         (concat "\x1b" (funcall fun "\x1b[33m test \x1b[0m"))))))
      (with-temp-buffer
        (should (equal (funcall fun "\x1b[") ""))
        (should (equal (funcall fun "\x1b[33m Z \x1b[0m")
                       (with-temp-buffer
                         (concat "\x1b[" (funcall fun "\x1b[33m Z \x1b[0m"))))))
      (with-temp-buffer
        (should (equal (funcall fun "\x1b a \x1b\x1b[\x1b[") "\x1b a \x1b\x1b["))
        (should (equal (funcall fun "\x1b[33m Z \x1b[0m")
                       (with-temp-buffer
                         (concat "\x1b[" (funcall fun "\x1b[33m Z \x1b[0m")))))))))

(provide 'ansi-color-tests)

;;; ansi-color-tests.el ends here
