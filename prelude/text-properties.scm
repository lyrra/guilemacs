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
            ;; Property change search
            next-single-property-change
            previous-single-property-change
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

    ;; Plain string - wrap it first, then add properties (Phase 3)
    ((string? obj)
     (let* ((wrapped (wrap-string obj))
            (new-intervals (add-properties-to-intervals
                            '() start end props)))
       (emacs-string-intervals-set! wrapped new-intervals)
       wrapped))  ; Return the wrapper!

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

;;; Property Change Search Functions

(define (next-single-property-change position prop obj limit)
  "Find next position where PROP changes in OBJ starting from POSITION.
Returns the position of the change, or LIMIT if no change found.
OBJ can be a buffer, string, or emacs-string wrapper.
LIMIT is optional - defaults to end of object if not provided."
  (let* ((intervals (cond
                     ((emacs-string? obj) (emacs-string-intervals obj))
                     ((string? obj) '())
                     (else (buffer-intervals-get obj))))
         (obj-end (cond
                   ((emacs-string? obj) (emacs-string-length obj))
                   ((string? obj) (string-length obj))
                   (else #f)))  ; For buffers, we don't know the end
         (actual-limit (if (and limit (not (eq? limit #nil)))
                          limit
                          obj-end))
         (current-val (interval-get-property-at intervals position prop)))

    ;; If no intervals or position is at/past limit, return limit
    (if (or (null? intervals)
            (and actual-limit (>= position actual-limit)))
        (or limit #nil)
        ;; Search through intervals for a change
        (let loop ((ints intervals)
                   (pos position))
          (cond
           ;; No more intervals - return limit
           ((null? ints)
            (or limit #nil))

           ;; Check current interval
           (else
            (let* ((int (car ints))
                   (int-start (interval-start int))
                   (int-end (interval-end int))
                   (int-val (plist-get (interval-plist int) prop)))

              (cond
               ;; This interval is entirely before our position - skip it
               ((<= int-end pos)
                (loop (cdr ints) pos))

               ;; We're inside this interval
               ((and (>= pos int-start) (< pos int-end))
                ;; Check if value differs from current
                (if (not (equal? int-val current-val))
                    ;; Value changed at start of this interval
                    (if (and actual-limit (>= int-start actual-limit))
                        (or limit #nil)
                        int-start)
                    ;; Value same, property changes at end of interval
                    (if (and actual-limit (>= int-end actual-limit))
                        (or limit #nil)
                        ;; Check if next interval exists and has same value
                        (if (null? (cdr ints))
                            ;; No next interval - change at end
                            int-end
                            (let ((next-val (plist-get (interval-plist (cadr ints)) prop)))
                              (if (equal? int-val next-val)
                                  ;; Same value continues - keep searching
                                  (loop (cdr ints) int-end)
                                  ;; Different value - change at end
                                  int-end))))))

               ;; We're before this interval - property changes at its start
               (else
                (if (and actual-limit (>= int-start actual-limit))
                    (or limit #nil)
                    int-start))))))))))

(define (previous-single-property-change position prop obj limit)
  "Find previous position where PROP changes in OBJ before POSITION.
Returns the position of the change, or LIMIT if no change found.
OBJ can be a buffer, string, or emacs-string wrapper.
LIMIT is optional - defaults to start of object (0) if not provided."
  (let* ((intervals (cond
                     ((emacs-string? obj) (emacs-string-intervals obj))
                     ((string? obj) '())
                     (else (buffer-intervals-get obj))))
         (actual-limit (if (and limit (not (eq? limit #nil)))
                          limit
                          0))
         ;; Get property value just before position
         (current-val (if (> position 0)
                         (interval-get-property-at intervals (- position 1) prop)
                         #nil)))

    ;; If no intervals or position is at/before limit, return limit
    (if (or (null? intervals)
            (<= position actual-limit))
        (or limit #nil)
        ;; Search backward through intervals for a change
        (let loop ((ints (reverse intervals))
                   (pos position))
          (cond
           ;; No more intervals - return limit
           ((null? ints)
            (or limit #nil))

           ;; Check current interval
           (else
            (let* ((int (car ints))
                   (int-start (interval-start int))
                   (int-end (interval-end int))
                   (int-val (plist-get (interval-plist int) prop)))

              (cond
               ;; This interval is entirely after our position - skip it
               ((>= int-start pos)
                (loop (cdr ints) pos))

               ;; We're inside this interval or just past it
               ((< int-start pos)
                ;; Check if value at end differs from current
                (if (and (<= int-end pos) (not (equal? int-val current-val)))
                    ;; Value changed at end of this interval
                    (if (<= int-end actual-limit)
                        (or limit #nil)
                        int-end)
                    ;; Check at start of interval
                    (if (<= int-start actual-limit)
                        (or limit #nil)
                        ;; Check if previous interval has different value
                        (if (null? (cdr ints))
                            (if (<= int-start actual-limit)
                                (or limit #nil)
                                int-start)
                            (let ((prev-val (plist-get (interval-plist (cadr ints)) prop)))
                              (if (equal? int-val prev-val)
                                  (loop (cdr ints) int-start)
                                  (if (<= int-start actual-limit)
                                      (or limit #nil)
                                      int-start)))))))

               (else
                (loop (cdr ints) pos))))))))))

;;; Module initialization

(format #t "~%;; text-properties.scm loaded (wrapper-based)~%")
