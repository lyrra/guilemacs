;;; string-operations.scm --- Wrapper-aware string operations  -*- lexical-binding: t; -*-

;; Copyright (C) 2025 Free Software Foundation, Inc.

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

;; This module provides wrapper-aware versions of string operations.
;; These functions detect emacs-string wrappers and preserve text
;; properties through operations like substring and concat.
;;
;; Key principle: When operating on wrapped strings, we must:
;; 1. Extract the intervals from the source
;; 2. Adjust/merge intervals as appropriate
;; 3. Return a new wrapper with the adjusted intervals

;;; Code:

(define-module (string-operations)
  #:use-module (emacs-string)
  #:use-module (intervals)
  #:use-module (ice-9 format)
  #:use-module (srfi srfi-1)  ; for 'any'
  #:export (substring-with-properties
            concat-with-properties
            upcase-with-properties
            downcase-with-properties
            ;; Helper for concat
            merge-intervals-concat))

;;; Save original Guile string functions

(define %guile-substring substring)
(define %guile-string-append string-append)
(define %guile-string-upcase string-upcase)
(define %guile-string-downcase string-downcase)

;;; Wrapper-aware substring

(define* (substring-with-properties str start #:optional end)
  "Extract substring from START to END, preserving text properties.
If STR is an emacs-string wrapper, properties are extracted and adjusted.
If STR is a plain string, this is equivalent to regular substring."
  (cond
    ;; Plain string - use original substring
    ((not (emacs-string? str))
     (if end
         (%guile-substring str start end)
         (%guile-substring str start)))

    ;; Wrapped string - preserve properties
    (else
     (let* ((content (emacs-string-content str))
            (actual-end (if end end (string-length content)))
            (new-content (%guile-substring content start actual-end))
            (old-intervals (emacs-string-intervals str)))

       ;; If no properties, just return plain string
       (if (null? old-intervals)
           new-content
           ;; Extract and adjust intervals for the substring
           (let ((new-intervals (extract-intervals old-intervals start actual-end)))
             (if (null? new-intervals)
                 new-content  ; No properties in this range
                 (make-emacs-string new-content new-intervals))))))))

;;; Wrapper-aware concat

(define (merge-intervals-concat strings)
  "Merge intervals from multiple strings for concatenation.
Returns interval list for the concatenated result.
Each string's intervals are shifted by the cumulative length."
  (let loop ((remaining strings)
             (offset 0)
             (result '()))
    (if (null? remaining)
        (reverse result)
        (let* ((str (car remaining))
               (content (emacs-string-content str))
               (len (string-length content))
               (intervals (if (emacs-string? str)
                             (emacs-string-intervals str)
                             '())))
          ;; Shift intervals by offset and add to result
          (let ((shifted (shift-intervals intervals offset)))
            (loop (cdr remaining)
                  (+ offset len)
                  (append (reverse shifted) result)))))))

(define (concat-with-properties . strings)
  "Concatenate strings, preserving text properties.
If any string is an emacs-string wrapper, properties are merged.
If all are plain strings, this is equivalent to regular string-append."
  ;; Check if any string has properties
  (let ((has-properties? (any emacs-string? strings)))
    (if (not has-properties?)
        ;; All plain - use fast path
        (apply %guile-string-append strings)
        ;; Has wrappers - merge properties
        (let* ((contents (map emacs-string-content strings))
               (result-content (apply %guile-string-append contents))
               (merged-intervals (merge-intervals-concat strings)))
          (if (null? merged-intervals)
              result-content
              (make-emacs-string result-content merged-intervals))))))

;;; Wrapper-aware case conversion

(define (upcase-with-properties str)
  "Convert string to uppercase, preserving text properties."
  (cond
    ((not (emacs-string? str))
     (%guile-string-upcase str))

    (else
     (let ((content (emacs-string-content str))
           (intervals (emacs-string-intervals str)))
       (make-emacs-string (%guile-string-upcase content) intervals)))))

(define (downcase-with-properties str)
  "Convert string to lowercase, preserving text properties."
  (cond
    ((not (emacs-string? str))
     (%guile-string-downcase str))

    (else
     (let ((content (emacs-string-content str))
           (intervals (emacs-string-intervals str)))
       (make-emacs-string (%guile-string-downcase content) intervals)))))

;;; Module initialization

(format #t "~%;; string-operations.scm loaded~%")
