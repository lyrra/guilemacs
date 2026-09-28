;;; xt-mouse-tests.el --- Test suite for xt-mouse.  -*- lexical-binding: t; -*-

;; Copyright (C) 2016-2025 Free Software Foundation, Inc.

;; Author: Philipp Stephani <phst@google.com>

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

;; xterm.el reads this flag while setting up a TTY.  That happens before
;; xt-mouse is necessarily loaded, so loaddefs (and ldefs-boot.el in
;; Guilemacs) must declare it.  Capture the startup state before the
;; require below defines the variable and could hide a missing autoload.
(defconst xt-mouse-tests--mode-called-predeclared-p
  (boundp 'xterm-mouse-mode-called))

(require 'xt-mouse)

(ert-deftest xt-mouse-mode-called-predeclared-at-startup ()
  (should xt-mouse-tests--mode-called-predeclared-p))

;; FIXME: this doesn't work when called inside a non-batch mode Emacs
;; session.
(defmacro with-xterm-mouse-mode (&rest body)
  "Run BODY with `xterm-mouse-mode' temporarily enabled."
  (declare (indent 0))
  (when noninteractive
    `(let ((width (frame-width))
           (height (frame-height)))
       (unwind-protect
           (progn
             ;; Make the frame huge so that the test input events below
             ;; don't hit the menu bar.
             (set-frame-width nil (max width 2000))
             (set-frame-height nil (max height 2000))
             (cl-letf (;; Reset XTerm parameters so that the tests don't
                       ;; get confused.
                       ((terminal-parameter nil 'xterm-mouse-x) nil)
                       ((terminal-parameter nil 'xterm-mouse-y) nil)
                       ((terminal-parameter nil 'xterm-mouse-last-down) nil)
                       ((terminal-parameter nil 'xterm-mouse-last-click) nil))
               (unwind-protect
                   (progn
                     ;; `xterm-mouse-mode' doesn't work in the initial
                     ;; terminal.  Since we can't create a second
                     ;; terminal in batch mode, fake it temporarily.
                     (cl-letf (((symbol-function 'send-string-to-terminal)
                                (lambda (&rest _args) nil))
                               ((symbol-function 'terminal-name)
                                (lambda (&optional _terminal) "fake-terminal")))
                       (xterm-mouse-mode 1))
                     ,@body)
                 (cl-letf (((symbol-function 'send-string-to-terminal)
                            (lambda (&rest _args) nil)))
                   (xterm-mouse-mode 0)))))
         (set-frame-width nil width)
         (set-frame-height nil height)))))


(ert-deftest xt-mouse-tracking-basic ()
  (should (equal (xterm-mouse-tracking-enable-sequence)
                 "\x1b[?1000h\x1b[?1003h\x1b[?1006h"))
  (should (equal (xterm-mouse-tracking-disable-sequence)
                 "\x1b[?1006l\x1b[?1003l\x1b[?1000l"))
  (with-xterm-mouse-mode
    (should xterm-mouse-mode)
    (should (terminal-parameter nil 'xterm-mouse-mode))
    (should-not (terminal-parameter nil 'xterm-mouse-utf-8))
    (let* ((unread-command-events (append "\x1b[M%\xD9\x81"
                                          "\x1b[M'\xD9\x81" nil))
           (key (read-key)))
      (should (consp key))
      (cl-destructuring-bind (event-type position . rest) key
        (should (equal event-type 'S-mouse-2))
        (should (consp position))
        (cl-destructuring-bind (_ _ xy . rest) position
          (should (equal xy '(184 . 95))))))))

(ert-deftest xt-mouse-tracking-utf-8 ()
  (let ((xterm-mouse-utf-8 t))
    (should (equal (xterm-mouse-tracking-enable-sequence)
                   "\x1b[?1000h\x1b[?1003h\x1b[?1005h\x1b[?1006h"))
    (should (equal (xterm-mouse-tracking-disable-sequence)
                   "\x1b[?1006l\x1b[?1005l\x1b[?1003l\x1b[?1000l"))
    (with-xterm-mouse-mode
      (should xterm-mouse-mode)
      (should (terminal-parameter nil 'xterm-mouse-mode))
      (should (terminal-parameter nil 'xterm-mouse-utf-8))
      ;; The keyboard driver doesn't decode bytes in
      ;; `unread-command-events'.
      (let* ((unread-command-events (append "\x1b[M%\u0640\u0131"
                                            "\x1b[M'\u0640\u0131" nil))
             (key (read-key)))
        (should (consp key))
        (cl-destructuring-bind (event-type position . rest) key
          (should (equal event-type 'S-mouse-2))
          (should (consp position))
          (cl-destructuring-bind (_ _ xy . rest) position
            (should (equal xy '(1567 . 271)))))))))

(ert-deftest xt-mouse-tracking-sgr ()
  (with-xterm-mouse-mode
    (should xterm-mouse-mode)
    (should (terminal-parameter nil 'xterm-mouse-mode))
    (should-not (terminal-parameter nil 'xterm-mouse-utf-8))
    (let* ((unread-command-events (append "\x1b[<5;1569;273;M"
                                          "\x1b[<5;1569;273;m" nil))
           (key (read-key)))
      (should (consp key))
      ;; The input translator records the click which read-key must return.
      (should (eq (car last-input-event) 'S-mouse-2))
      (cl-destructuring-bind (event-type position . rest) key
        (should (equal event-type 'S-mouse-2))
        (should (consp position))
        (cl-destructuring-bind (_ _ xy . rest) position
          (should (equal xy '(1568 . 271))))))))

(ert-deftest xt-mouse-sgr-down-event-regexp-replacement ()
  ;; This replacement is used when an SGR release arrives without a
  ;; remembered down event.  Nil concat fragments must be empty strings.
  (should (equal (concat nil "S-" nil "mouse-2") "S-mouse-2"))
  (should (equal (replace-regexp-in-string
                  "\\`\\([ACMHSs]-\\)*" "\\&down-" "S-mouse-2" t)
                 "S-down-mouse-2")))

(ert-deftest xt-mouse-sgr-input-parser-result-before-key-sequence ()
  ;; Observe the real parser while read-key consumes the report.  The
  ;; parser result is a click; read-key currently returns a bad down event.
  (with-xterm-mouse-mode
    (let ((read-sequence (symbol-function
                          'xterm-mouse--read-event-sequence))
          (parsed-events nil)
          (unread-command-events (append "\x1b[<5;1569;273;M"
                                         "\x1b[<5;1569;273;m" nil)))
      (cl-letf (((symbol-function 'xterm-mouse--read-event-sequence)
                 (lambda (extension)
                   (let ((event (funcall read-sequence extension)))
                     (push (car event) parsed-events)
                     event))))
        (read-key))
      (should (equal (nreverse parsed-events) '(S-mouse-2))))))

(ert-deftest xt-mouse-sgr-modifier-prefixes ()
  ;; Exercise event-name construction directly.  SGR code bits 4, 8, and
  ;; 16 represent Shift, Meta, and Control, respectively.
  (dolist (case '((1 down-mouse-2)
                  (5 S-down-mouse-2)
                  (9 M-down-mouse-2)
                  (13 M-S-down-mouse-2)
                  (17 C-down-mouse-2)
                  (21 C-S-down-mouse-2)
                  (25 C-M-down-mouse-2)
                  (29 C-M-S-down-mouse-2)))
    (let ((reports (list (cons (car case) 59)
                         (cons 2 59)
                         (cons 3 77))))
      (cl-letf (((symbol-function 'xterm-mouse--read-number-from-terminal)
                 (lambda (_extension) (pop reports))))
        (should (equal (car (xterm-mouse--read-event-sequence 1006))
                       (cadr case)))))))

;;; xt-mouse-tests.el ends here
