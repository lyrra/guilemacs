;;; emacs-string.scm --- String wrapper with text properties  -*- lexical-binding: t; -*-

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

;; This module implements the emacs-string wrapper structure that pairs
;; string content with text property intervals. This is the core data
;; structure for text properties in Guilemacs, mirroring how C Emacs
;; stores properties in `struct Lisp_String` but in pure Scheme.
;;
;; The wrapper solves the fundamental problem with hash tables: string
;; identity is not stable across operations, making external tracking
;; unreliable. By embedding intervals directly in the wrapper, properties
;; are always attached to the string.

;;; Code:

(define-module (emacs-string)
  #:use-module (srfi srfi-9)  ; define-record-type
  #:use-module (ice-9 format)
  #:export (make-emacs-string
            emacs-string?
            emacs-string-predicate  ; Runtime-callable version for C
            emacs-string-content
            emacs-string-intervals
            emacs-string-intervals-runtime  ; Runtime-callable version for C
            emacs-string-intervals-set!
            emacs-string-length
            ;; Conversion utilities
            wrap-string
            unwrap-string
            deep-unwrap-for-printing  ; Phase 4: for prin1-to-string
            ;; Wrapper check
            has-properties?))

;;; Data Structure

;; The wrapper structure
;; - content: The actual Guile string (SCM string)
;; - intervals: List of <interval> records (from intervals.scm)
(define-record-type <emacs-string>
  (%make-emacs-string content intervals)
  emacs-string?
  (content %emacs-string-content)
  (intervals emacs-string-intervals emacs-string-intervals-set!))

;;; Runtime-callable predicate for C code
;; emacs-string? might be a macro in some Guile versions, so we wrap it
(define (emacs-string-predicate obj)
  "Runtime-callable wrapper for emacs-string? predicate.
This is needed because C code can't call macros directly."
  (emacs-string? obj))

;;; Runtime-callable accessor for C code
;; SRFI-9 record accessors are syntax transformers, not procedures
(define (emacs-string-intervals-runtime obj)
  "Runtime-callable wrapper for emacs-string-intervals accessor.
This is needed because SRFI-9 accessors are syntax transformers, not procedures."
  (emacs-string-intervals obj))

;;; Constructors

(define (make-emacs-string content . intervals)
  "Create an emacs-string wrapper.
CONTENT must be a Guile string.
INTERVALS is optional - if not provided, empty list is used."
  (cond
    ((not (string? content))
     (error "make-emacs-string: content must be a string, got" content))
    ((null? intervals)
     (%make-emacs-string content '()))
    (else
     (%make-emacs-string content (car intervals)))))

;;; Accessors

(define (emacs-string-content obj)
  "Get string content from OBJ.
If OBJ is an emacs-string wrapper, extract the content.
If OBJ is a plain string, return it as-is.
This auto-unwrapping makes functions work with both wrapped and plain strings."
  (if (emacs-string? obj)
      (%emacs-string-content obj)
      obj))

(define (emacs-string-length obj)
  "Get length of string in OBJ.
Works with both wrapped strings and plain strings."
  (string-length (emacs-string-content obj)))

;;; Conversion Utilities

(define (wrap-string str)
  "Wrap a plain string with no properties.
If STR is already wrapped, return it unchanged.
If STR is a plain string, wrap it with empty interval list."
  (cond
    ((emacs-string? str) str)
    ((string? str) (%make-emacs-string str '()))
    (else (error "wrap-string: argument must be a string" str))))

(define (unwrap-string estr)
  "Extract content string from wrapper.
If ESTR is a wrapper, extract the content.
If ESTR is already a plain string, return it as-is."
  (if (emacs-string? estr)
      (%emacs-string-content estr)
      estr))

(define (deep-unwrap-for-printing obj)
  "Recursively unwrap emacs-strings in OBJ for printing.
This is used by prin1-to-string to ensure wrapper objects don't appear in output.
- Unwraps emacs-string wrappers to plain strings
- Recursively processes lists
- Recursively processes vectors
- Leaves other objects unchanged"
  (cond
    ((emacs-string? obj)
     ;; Unwrap the string
     (%emacs-string-content obj))
    ((pair? obj)
     ;; Recursively unwrap car and cdr
     (cons (deep-unwrap-for-printing (car obj))
           (deep-unwrap-for-printing (cdr obj))))
    ((vector? obj)
     ;; Recursively unwrap vector elements
     (list->vector (map deep-unwrap-for-printing (vector->list obj))))
    (else
     ;; Return other objects as-is
     obj)))

;;; Predicates

(define (has-properties? obj)
  "Return #t if OBJ is an emacs-string with non-empty intervals.
Plain strings always return #f."
  (and (emacs-string? obj)
       (not (null? (emacs-string-intervals obj)))))

;;; Debugging

(define (emacs-string->string estr)
  "Convert emacs-string to readable string for debugging."
  (if (not (emacs-string? estr))
      (format #f "~s" estr)
      (let ((content (%emacs-string-content estr))
            (intervals (emacs-string-intervals estr)))
        (format #f "#<emacs-string ~s intervals:~a>"
                content
                (length intervals)))))

;;; Module initialization

(format #t "~%;; emacs-string.scm loaded~%")

;; Note: Custom printer for emacs-string wrappers is not implemented yet.
;; Guile's set-record-type-printer! is not available in Guile 3.0.8.
;; For now, avoid printing wrappers with %S - use %s or unwrap first.
