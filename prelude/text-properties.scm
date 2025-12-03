;;; text-properties.scm --- Text property support in Guile  -*- lexical-binding: t; -*-

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

;; This module implements text properties for Guile strings and buffers.
;; Text properties in Emacs allow associating arbitrary metadata with
;; ranges of text. Since Guile uses native SCM strings (not struct Lisp_String),
;; we use weak-key hash tables to store interval trees for each string/buffer.

;;; Code:

(define-module (text-properties)
  #:use-module (ice-9 format)
  #:use-module (srfi srfi-9)  ; define-record-type
  #:export (string-intervals-get
            string-intervals-set!
            buffer-intervals-get
            buffer-intervals-set!
            text-properties-at
            get-text-property
            add-text-properties
            put-text-property
            propertize
            ;; C bridge wrapper functions
            get-interval-start
            get-interval-end
            get-interval-plist))

;;; Storage

;; Use hashq tables for object identity (not content equality)
;; This ensures different string objects don't share properties
(define *string-text-properties* (make-hash-table))
(define *buffer-text-properties* (make-hash-table))

;;; Data Structures

;; An interval represents a contiguous range of text with properties
;; Intervals are non-overlapping and partition the text
(define-record-type <interval>
  (make-interval start end plist)
  interval?
  (start interval-start interval-start-set!)
  (end interval-end interval-end-set!)
  (plist interval-plist interval-plist-set!))

;;; Property List Operations

(define (plist-get plist prop)
  "Get PROP from PLIST (property list)."
  (let loop ((lst plist))
    (cond
      ((null? lst) #nil)
      ((eq? (car lst) prop) (cadr lst))
      (else (loop (cddr lst))))))

(define (plist-put plist prop value)
  "Add or replace PROP with VALUE in PLIST."
  (let loop ((lst plist) (result '()))
    (cond
      ((null? lst)
       ;; Property not found, add it
       (reverse (cons value (cons prop result))))
      ((eq? (car lst) prop)
       ;; Replace existing value
       (append (reverse result) (cons prop (cons value (cddr lst)))))
      (else
       ;; Keep looking
       (loop (cddr lst) (cons (cadr lst) (cons (car lst) result)))))))

(define (plist-equal? p1 p2)
  "Return #t if property lists P1 and P2 are equal."
  (and (= (length p1) (length p2))
       (let loop ((lst p1))
         (or (null? lst)
             (and (equal? (plist-get p2 (car lst)) (cadr lst))
                  (loop (cddr lst)))))))

;;; Interval Operations

(define (find-interval-at intervals pos)
  "Find the interval in INTERVALS containing POS."
  (let loop ((ints intervals))
    (cond
      ((null? ints) #f)
      ((and (>= pos (interval-start (car ints)))
            (< pos (interval-end (car ints))))
       (car ints))
      (else (loop (cdr ints))))))

(define (merge-adjacent-intervals intervals)
  "Merge adjacent intervals with identical properties."
  (if (< (length intervals) 2)
      intervals
      (let loop ((remaining intervals) (result '()))
        (if (null? (cdr remaining))
            (reverse (cons (car remaining) result))
            (let ((int1 (car remaining))
                  (int2 (cadr remaining)))
              (if (and (= (interval-end int1) (interval-start int2))
                       (plist-equal? (interval-plist int1) (interval-plist int2)))
                  ;; Merge the two intervals
                  (loop (cons (make-interval (interval-start int1)
                                            (interval-end int2)
                                            (interval-plist int1))
                             (cddr remaining))
                        result)
                  ;; Keep them separate
                  (loop (cdr remaining) (cons int1 result))))))))

(define (split-interval interval pos)
  "Split INTERVAL at POS. Return (left . right)."
  (if (or (<= pos (interval-start interval))
          (>= pos (interval-end interval)))
      (cons interval #f)
      (cons (make-interval (interval-start interval) pos
                          (interval-plist interval))
            (make-interval pos (interval-end interval)
                          (interval-plist interval)))))

(define (add-properties-to-intervals intervals start end new-props)
  "Add NEW-PROPS to INTERVALS in range [START, END)."
  (if (null? intervals)
      ;; No intervals yet, create one covering the range
      (list (make-interval start end new-props))
      (let loop ((ints intervals) (result '()))
        (cond
          ((null? ints)
           ;; Done processing
           (merge-adjacent-intervals (reverse result)))

          ((>= (interval-start (car ints)) end)
           ;; This interval is after our range, keep rest as-is
           (merge-adjacent-intervals (append (reverse result) ints)))

          ((< (interval-end (car ints)) start)
           ;; This interval is before our range, keep it
           (loop (cdr ints) (cons (car ints) result)))

          (else
           ;; This interval overlaps our range
           (let* ((int (car ints))
                  (int-start (interval-start int))
                  (int-end (interval-end int))
                  (int-props (interval-plist int)))

             ;; Handle the part before START (if any)
             (define before-part
               (if (< int-start start)
                   (list (make-interval int-start start int-props))
                   '()))

             ;; Handle the overlapping part
             (define overlap-start (max int-start start))
             (define overlap-end (min int-end end))
             (define merged-props
               (let merge-loop ((props new-props) (base int-props))
                 (if (null? props)
                     base
                     (merge-loop (cddr props)
                                (plist-put base (car props) (cadr props))))))
             (define overlap-part
               (list (make-interval overlap-start overlap-end merged-props)))

             ;; Handle the part after END (if any)
             (define after-part
               (if (> int-end end)
                   (list (make-interval end int-end int-props))
                   '()))

             ;; Continue with remaining intervals
             (loop (cdr ints)
                   (append after-part overlap-part before-part result))))))))

;;; C Bridge - Wrapper functions for record accessors
;;; (needed because record accessors are syntax transformers)

(define (get-interval-start interval)
  "Get the start position of INTERVAL (for C bridge)."
  (interval-start interval))

(define (get-interval-end interval)
  "Get the end position of INTERVAL (for C bridge)."
  (interval-end interval))

(define (get-interval-plist interval)
  "Get the property list of INTERVAL (for C bridge)."
  (interval-plist interval))

;;; Public API - Storage Access

(define (string-intervals-get string)
  "Get interval list for STRING."
  (hashq-ref *string-text-properties* string '()))

(define (string-intervals-set! string intervals)
  "Set interval list for STRING."
  (if (null? intervals)
      (hashq-remove! *string-text-properties* string)
      (hashq-set! *string-text-properties* string intervals)))

(define (buffer-intervals-get buffer)
  "Get interval list for BUFFER."
  (hashq-ref *buffer-text-properties* buffer '()))

(define (buffer-intervals-set! buffer intervals)
  "Set interval list for BUFFER."
  (if (null? intervals)
      (hashq-remove! *buffer-text-properties* buffer)
      (hashq-set! *buffer-text-properties* buffer intervals)))

;;; Public API - Text Property Functions

(define (text-properties-at pos object)
  "Return property list of text at POS in OBJECT.
OBJECT can be a string or buffer. If nil, use current buffer."
  (let* ((is-string (string? object))
         (intervals (if is-string
                       (string-intervals-get object)
                       (buffer-intervals-get object)))
         (interval (find-interval-at intervals pos)))
    (if interval
        (interval-plist interval)
        #nil)))

(define (get-text-property pos prop object)
  "Return value of PROP property at POS in OBJECT."
  (let ((plist (text-properties-at pos object)))
    (if (eq? plist #nil)
        #nil
        (plist-get plist prop))))

(define (add-text-properties start end properties object)
  "Add PROPERTIES to text from START to END in OBJECT.
PROPERTIES is a property list. Returns t if any property changed."
  ;; Debug: check for negative positions
  (when (or (< start 0) (< end 0))
    (format #t "ERROR in add-text-properties: start=~a end=~a object-type=~a~%"
            start end (if (string? object) "string" "buffer"))
    (format #t "  Stack trace:~%")
    (backtrace))
  (let* ((is-string (string? object))
         (old-intervals (if is-string
                           (string-intervals-get object)
                           (buffer-intervals-get object)))
         (new-intervals (add-properties-to-intervals old-intervals start end properties)))
    (if is-string
        (string-intervals-set! object new-intervals)
        (buffer-intervals-set! object new-intervals))
    ;; Return t if changed (simplified - always return t for now)
    #t))

(define (put-text-property start end prop value object)
  "Set PROP to VALUE in text from START to END in OBJECT."
  (add-text-properties start end (list prop value) object))

(define (propertize string . properties)
  "Return a copy of STRING with text properties added.
Properties are specified as keyword-value pairs."
  ;; Always create a new string (ensures unique identity)
  (let* ((new-string (string-copy string))
         (len (string-length new-string))
         (interval (make-interval 0 len properties)))
    (string-intervals-set! new-string (list interval))
    new-string))

;;; Module initialization

(format #t "~%;; text-properties.scm loaded~%")
