;;; text-properties.scm --- Text property operations on wrappers  -*- lexical-binding: t; -*-

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

;; This module implements text property operations using the emacs-string
;; wrapper structure. This replaces the broken hash table approach with
;; a sound architecture where properties are embedded in the wrapper.
;;
;; Key functions:
;; - propertize: Create a new wrapped string with properties
;; - get-text-property: Get property value at position
;; - add-text-properties: Add properties to range
;; - text-properties-at: Get all properties at position
;;
;; For buffers, we still use a hash table since buffer objects have
;; stable identity.

;;; Code:

(define-module (text-properties)
  #:use-module (emacs-string)
  #:use-module (intervals)
  #:use-module (ice-9 format)
  #:export (;; String property operations
            propertize
            get-text-property
            add-text-properties
            put-text-property
            text-properties-at
            ;; Buffer property storage
            buffer-intervals-get
            buffer-intervals-set!
            buffer-add-text-properties
            buffer-put-text-property
            buffer-get-text-property
            buffer-text-properties-at))

;;; Buffer Property Storage
;;
;; Buffers have stable identity, so hash table is fine for them

(define *buffer-text-properties* (make-hash-table))

(define (buffer-intervals-get buffer)
  "Get interval list for BUFFER."
  (hashq-ref *buffer-text-properties* buffer '()))

(define (buffer-intervals-set! buffer intervals)
  "Set interval list for BUFFER."
  (if (null? intervals)
      (hashq-remove! *buffer-text-properties* buffer)
      (hashq-set! *buffer-text-properties* buffer intervals)))

;;; String Property Operations (using wrapper)

(define (propertize str . props)
  "Create new string with properties.
STR can be a plain string or an emacs-string wrapper.
PROPS are alternating keys and values: (propertize \"hello\" 'face 'bold)
Returns an emacs-string wrapper."
  (let* ((content (if (emacs-string? str)
                      (string-copy (emacs-string-content str))
                      (string-copy str)))
         (plist (parse-plist props))
         (len (string-length content))
         (interval (make-interval 0 len plist)))
    (make-emacs-string content (list interval))))

(define (get-text-property pos prop obj)
  "Get value of PROP at POS in OBJ.
OBJ can be:
  - An emacs-string wrapper (string with properties)
  - A plain string (returns #nil)
  - A buffer (looks up in buffer property table)
  - #nil (uses current buffer - TODO)
Returns property value or #nil if not found."
  (cond
    ;; Wrapped string - get from intervals
    ((emacs-string? obj)
     (let ((intervals (emacs-string-intervals obj)))
       (interval-get-property-at intervals pos prop)))

    ;; Plain string - no properties
    ((string? obj)
     #nil)

    ;; Buffer - get from buffer property table
    (else
     (let ((intervals (buffer-intervals-get obj)))
       (interval-get-property-at intervals pos prop)))))

(define (text-properties-at pos obj)
  "Get all properties at POS in OBJ.
Returns property list or #nil."
  (cond
    ;; Wrapped string
    ((emacs-string? obj)
     (let ((intervals (emacs-string-intervals obj)))
       (interval-get-plist-at intervals pos)))

    ;; Plain string
    ((string? obj)
     #nil)

    ;; Buffer
    (else
     (let ((intervals (buffer-intervals-get obj)))
       (interval-get-plist-at intervals pos)))))

(define (add-text-properties start end props obj)
  "Add PROPS to text from START to END in OBJ.
PROPS is a property list.
For strings: OBJ must be an emacs-string wrapper (modifies in place).
For buffers: OBJ is a buffer object.
Returns #t if properties were added."
  (cond
    ;; Wrapped string - modify intervals in place
    ((emacs-string? obj)
     (let* ((old-intervals (emacs-string-intervals obj))
            (new-intervals (add-properties-to-intervals
                            old-intervals start end props)))
       (emacs-string-intervals-set! obj new-intervals)
       #t))

    ;; Plain string - cannot add properties to plain string!
    ((string? obj)
     (format #t "WARNING: Cannot add properties to plain string, must be wrapped~%")
     #f)

    ;; Buffer
    (else
     (let* ((old-intervals (buffer-intervals-get obj))
            (new-intervals (add-properties-to-intervals
                            old-intervals start end props)))
       (buffer-intervals-set! obj new-intervals)
       #t))))

(define (put-text-property start end prop value obj)
  "Set PROP to VALUE in text from START to END in OBJ."
  (add-text-properties start end (list prop value) obj))

;;; Buffer-specific aliases

(define (buffer-add-text-properties buffer start end props)
  "Add PROPS to buffer text from START to END."
  (add-text-properties start end props buffer))

(define (buffer-put-text-property buffer start end prop value)
  "Set PROP to VALUE in buffer from START to END."
  (put-text-property start end prop value buffer))

(define (buffer-get-text-property buffer pos prop)
  "Get PROP value at POS in BUFFER."
  (get-text-property pos prop buffer))

(define (buffer-text-properties-at buffer pos)
  "Get all properties at POS in BUFFER."
  (text-properties-at pos buffer))

;;; Module initialization

(format #t "~%;; text-properties.scm loaded (wrapper-based)~%")
