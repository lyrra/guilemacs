;;; intervals.scm --- Interval management for text properties  -*- lexical-binding: t; -*-

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

;; This module implements interval trees for storing text properties.
;; An interval represents a contiguous range of text with associated
;; properties (stored as a property list).
;;
;; Key insights:
;; - Intervals are NON-OVERLAPPING - they partition the text
;; - Each interval has a start position, end position, and plist
;; - We start with a simple list implementation, can upgrade to tree later
;; - Adjacent intervals with identical properties are merged

;;; Code:

(define-module (intervals)
  #:use-module (srfi srfi-9)   ; define-record-type
  #:use-module (srfi srfi-1)   ; list utilities
  #:use-module (ice-9 format)
  #:export (;; Interval record
            make-interval
            interval?
            interval-start
            interval-end
            interval-plist
            interval-plist-set!
            ;; Interval operations
            find-interval-at
            interval-get-property-at
            interval-get-plist-at
            add-properties-to-intervals
            merge-adjacent-intervals
            split-interval
            extract-intervals
            shift-intervals
            ;; Property list operations
            plist-get
            plist-put
            plist-equal?
            parse-plist
            ;; C bridge accessors
            get-interval-start
            get-interval-end
            get-interval-plist))

;;; Data Structures

(define-record-type <interval>
  (make-interval start end plist)
  interval?
  (start interval-start interval-start-set!)
  (end interval-end interval-end-set!)
  (plist interval-plist interval-plist-set!))

;;; Property List Operations

(define (plist-get plist prop)
  "Get PROP from PLIST (property list).
Returns #nil if not found."
  (let loop ((lst plist))
    (cond
      ((null? lst) #nil)
      ((eq? (car lst) prop) (cadr lst))
      (else (loop (cddr lst))))))

(define (plist-put plist prop value)
  "Add or replace PROP with VALUE in PLIST.
Returns new plist."
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

(define (parse-plist props)
  "Parse property list from list of alternating keys and values.
Example: '(face bold mouse-face highlight) -> same list
Validates that length is even."
  (when (odd? (length props))
    (error "parse-plist: property list must have even length" props))
  props)

;;; Interval Search Operations

(define (find-interval-at intervals pos)
  "Find the interval in INTERVALS containing POS.
Returns the interval or #f if not found."
  (let loop ((ints intervals))
    (cond
      ((null? ints) #f)
      ((and (>= pos (interval-start (car ints)))
            (< pos (interval-end (car ints))))
       (car ints))
      (else (loop (cdr ints))))))

(define (interval-get-property-at intervals pos prop)
  "Get value of PROP at POS in INTERVALS.
Returns #nil if no interval at POS or property not found."
  (let ((interval (find-interval-at intervals pos)))
    (if interval
        (plist-get (interval-plist interval) prop)
        #nil)))

(define (interval-get-plist-at intervals pos)
  "Get all properties at POS in INTERVALS.
Returns plist or #nil if no interval at POS."
  (let ((interval (find-interval-at intervals pos)))
    (if interval
        (interval-plist interval)
        #nil)))

;;; Interval Manipulation

(define (split-interval interval pos)
  "Split INTERVAL at POS. Return (left . right).
If POS is outside interval bounds, return (interval . #f)."
  (if (or (<= pos (interval-start interval))
          (>= pos (interval-end interval)))
      (cons interval #f)
      (cons (make-interval (interval-start interval) pos
                          (interval-plist interval))
            (make-interval pos (interval-end interval)
                          (interval-plist interval)))))

(define (merge-adjacent-intervals intervals)
  "Merge adjacent intervals with identical properties.
Returns new interval list."
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

(define (add-properties-to-intervals intervals start end new-props)
  "Add NEW-PROPS to INTERVALS in range [START, END).
Returns new interval list."
  (if (null? intervals)
      ;; No intervals yet, create one covering the range
      (list (make-interval start end new-props))
      (let loop ((ints intervals) (result '()) (added-new? #f))
        (cond
          ((null? ints)
           ;; Done processing - if we haven't added the new interval yet, add it now
           (if added-new?
               (merge-adjacent-intervals (reverse result))
               (merge-adjacent-intervals (reverse (cons (make-interval start end new-props) result)))))

          ((>= (interval-start (car ints)) end)
           ;; This interval is after our range
           ;; Add new interval if not already added, then keep rest as-is
           (if added-new?
               (merge-adjacent-intervals (append (reverse result) ints))
               (merge-adjacent-intervals (append (reverse (cons (make-interval start end new-props) result)) ints))))

          ((<= (interval-end (car ints)) start)
           ;; This interval is before our range (or adjacent), keep it
           (loop (cdr ints) (cons (car ints) result) added-new?))

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
             ;; Mark that we've added the new interval (it's in overlap-part)
             (loop (cdr ints)
                   (append after-part overlap-part before-part result)
                   #t)))))))  ; added-new? = #t

(define (extract-intervals intervals start end)
  "Extract intervals from [START, END), adjusting positions.
Returns new interval list with positions adjusted to start at 0."
  (if (null? intervals)
      '()
      (let loop ((ints intervals) (result '()))
        (cond
          ((null? ints)
           (reverse result))

          ((>= (interval-start (car ints)) end)
           ;; Past our range, done
           (reverse result))

          ((< (interval-end (car ints)) start)
           ;; Before our range, skip
           (loop (cdr ints) result))

          (else
           ;; Overlaps our range
           (let* ((int (car ints))
                  (int-start (interval-start int))
                  (int-end (interval-end int))
                  (int-props (interval-plist int))
                  ;; Clip to [start, end) and adjust positions
                  (new-start (max 0 (- int-start start)))
                  (new-end (min (- end start) (- int-end start)))
                  (new-interval (make-interval new-start new-end int-props)))
             (loop (cdr ints) (cons new-interval result))))))))

(define (shift-intervals intervals offset)
  "Shift all intervals by OFFSET.
Returns new interval list."
  (map (lambda (int)
         (make-interval (+ (interval-start int) offset)
                       (+ (interval-end int) offset)
                       (interval-plist int)))
       intervals))

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

;;; Module initialization

(format #t "~%;; intervals.scm loaded~%")
