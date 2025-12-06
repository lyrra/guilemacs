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
            remove-text-properties
            set-text-properties
            ;; Property change search
            next-property-change
            previous-property-change
            next-single-property-change
            previous-single-property-change
            text-property-any
            text-property-not-all
            ;; Buffer property storage
            buffer-intervals-get
            buffer-intervals-set!
            buffer-add-text-properties
            buffer-put-text-property
            buffer-get-text-property
            buffer-text-properties-at
            ;; Buffer modification hooks
            buffer-on-insert
            buffer-on-delete))

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

               ;; We're before this interval
               (else
                ;; Check if property value changes at start of this interval
                (if (not (equal? int-val current-val))
                    ;; Property changes at start of this interval
                    (if (and actual-limit (>= int-start actual-limit))
                        (or limit #nil)
                        int-start)
                    ;; Property value is same, keep searching
                    (loop (cdr ints) int-start)))))))))))

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

(define (next-property-change position object limit)
  "Find next position where ANY property changes in OBJECT starting from POSITION.
Returns the position of the change, or LIMIT if no change found.
OBJECT can be a buffer, string, or emacs-string wrapper.
LIMIT is optional - defaults to end of object if not provided."
  (let* ((intervals (cond
                     ((emacs-string? object) (emacs-string-intervals object))
                     ((string? object) '())
                     (else (buffer-intervals-get object))))
         (obj-end (cond
                   ((emacs-string? object) (emacs-string-length object))
                   ((string? object) (string-length object))
                   (else #f)))
         (actual-limit (if (and limit (not (eq? limit #nil)))
                          limit
                          obj-end)))

    ;; If no intervals, no property changes
    (if (null? intervals)
        (or limit #nil)
        ;; Find the next interval boundary after position
        (let loop ((ints intervals))
          (cond
           ((null? ints)
            (or limit #nil))

           (else
            (let* ((int (car ints))
                   (int-start (interval-start int))
                   (int-end (interval-end int)))

              (cond
               ;; Interval is entirely before position - skip
               ((<= int-end position)
                (loop (cdr ints)))

               ;; We're before this interval (strictly less than start)
               ((< position int-start)
                ;; Next change is at start of this interval
                (if (and actual-limit (>= int-start actual-limit))
                    (or limit #nil)
                    int-start))

               ;; We're inside this interval
               ((< position int-end)
                ;; Next change is at end of this interval
                (if (and actual-limit (>= int-end actual-limit))
                    (or limit #nil)
                    int-end))

               ;; Shouldn't reach here
               (else
                (loop (cdr ints)))))))))))

(define (previous-property-change position object limit)
  "Find previous position where ANY property changes in OBJECT before POSITION.
Returns the position of the change, or LIMIT if no change found.
OBJECT can be a buffer, string, or emacs-string wrapper.
LIMIT is optional - defaults to start of object (0) if not provided."
  (let* ((intervals (cond
                     ((emacs-string? object) (emacs-string-intervals object))
                     ((string? object) '())
                     (else (buffer-intervals-get object))))
         (actual-limit (if (and limit (not (eq? limit #nil)))
                          limit
                          0)))

    ;; If no intervals, no property changes
    (if (null? intervals)
        (or limit #nil)
        ;; Find the previous interval boundary before position
        (let loop ((ints (reverse intervals)))
          (cond
           ((null? ints)
            (or limit #nil))

           (else
            (let* ((int (car ints))
                   (int-start (interval-start int))
                   (int-end (interval-end int)))

              (cond
               ;; Interval is entirely after position - skip
               ((>= int-start position)
                (loop (cdr ints)))

               ;; Position is after end of this interval
               ((> position int-end)
                ;; Previous change is at end of this interval
                (if (<= int-end actual-limit)
                    (or limit #nil)
                    int-end))

               ;; We're inside this interval
               ((>= position int-start)
                ;; Previous change is at start of this interval
                (if (<= int-start actual-limit)
                    (or limit #nil)
                    int-start))

               ;; Shouldn't reach here
               (else
                (loop (cdr ints)))))))))))

;;; Property Removal and Setting Functions (Phase 5)

(define (remove-text-properties start end props obj)
  "Remove properties in PROPS from text in range [START, END) in OBJ.
PROPS is a list of property names to remove.
Returns #t if any properties were removed, #nil otherwise."
  (let* ((intervals (cond
                     ((emacs-string? obj) (emacs-string-intervals obj))
                     ((string? obj) '())
                     (else (buffer-intervals-get obj))))
         (removed? #f))

    (if (null? intervals)
        #nil
        (let loop ((ints intervals) (result '()) (pos start))
          (cond
            ;; Processed all intervals
            ((null? ints)
             (let ((new-intervals (merge-adjacent-intervals (reverse result))))
               (cond
                 ((emacs-string? obj)
                  (emacs-string-intervals-set! obj new-intervals)
                  removed?)
                 ((string? obj) #nil)
                 (else
                  (buffer-intervals-set! obj new-intervals)
                  removed?))))

            ;; Current interval
            (else
             (let* ((int (car ints))
                    (int-start (interval-start int))
                    (int-end (interval-end int))
                    (int-plist (interval-plist int)))

               (cond
                 ;; Interval completely before range - keep as-is
                 ((<= int-end start)
                  (loop (cdr ints) (cons int result) int-end))

                 ;; Interval completely after range - keep rest as-is
                 ((>= int-start end)
                  (merge-adjacent-intervals (append (reverse result) ints)))

                 ;; Interval overlaps range - remove properties
                 (else
                  ;; Part before range (if any)
                  (let* ((before-part (if (< int-start start)
                                          (list (make-interval int-start start int-plist))
                                          '()))
                         ;; Overlapping part - remove specified properties
                         (overlap-start (max int-start start))
                         (overlap-end (min int-end end))
                         ;; Remove each property in props from plist
                         (new-plist (let remove-loop ((plist int-plist) (props-to-remove props))
                                     (if (null? props-to-remove)
                                         plist
                                         (let ((without-prop (remove-from-plist plist (car props-to-remove))))
                                           (when (not (equal? plist without-prop))
                                             (set! removed? #t))
                                           (remove-loop without-prop (cdr props-to-remove))))))
                         (overlap-part (if (null? new-plist)
                                          '()
                                          (list (make-interval overlap-start overlap-end new-plist))))
                         ;; Part after range (if any)
                         (after-part (if (> int-end end)
                                        (list (make-interval end int-end int-plist))
                                        '())))

                    (loop (cdr ints)
                          (append after-part overlap-part before-part result)
                          overlap-end)))))))))))

(define (remove-from-plist plist prop)
  "Remove PROP from PLIST. Returns new plist."
  (let loop ((lst plist) (result '()))
    (cond
      ((null? lst) (reverse result))
      ((eq? (car lst) prop)
       ;; Found property - skip it and its value
       (append (reverse result) (cddr lst)))
      (else
       ;; Keep property and value
       (loop (cddr lst) (cons (cadr lst) (cons (car lst) result)))))))

(define (set-text-properties start end props obj)
  "Set properties to PROPS for text in range [START, END) in OBJ.
This replaces all existing properties in the range with PROPS.
Returns #t."
  (let* ((intervals (cond
                     ((emacs-string? obj) (emacs-string-intervals obj))
                     ((string? obj) '())
                     (else (buffer-intervals-get obj)))))

    ;; Remove all existing intervals in range, then add new one
    (let loop ((ints intervals) (result '()))
      (cond
        ;; Processed all intervals
        ((null? ints)
         (let* ((cleared (reverse result))
                ;; Add new interval with props
                (new-interval (if (null? props)
                                 '()
                                 (list (make-interval start end props))))
                (merged (merge-adjacent-intervals
                         (if (null? new-interval)
                             cleared
                             (insert-sorted new-interval cleared)))))
           (cond
             ((emacs-string? obj)
              (emacs-string-intervals-set! obj merged))
             ((string? obj) #f)
             (else
              (buffer-intervals-set! obj merged)))
           #t))

        ;; Current interval
        (else
         (let* ((int (car ints))
                (int-start (interval-start int))
                (int-end (interval-end int))
                (int-plist (interval-plist int)))

           (cond
             ;; Interval completely before range - keep as-is
             ((<= int-end start)
              (loop (cdr ints) (cons int result)))

             ;; Interval completely after range - keep rest
             ((>= int-start end)
              (append (reverse result) ints))

             ;; Interval overlaps range - split and clear
             (else
              ;; Part before (keep properties)
              (let* ((before (if (< int-start start)
                                (list (make-interval int-start start int-plist))
                                '()))
                     ;; Part after (keep properties)
                     (after (if (> int-end end)
                               (list (make-interval end int-end int-plist))
                               '())))
                (loop (cdr ints) (append after before result)))))))))))

(define (insert-sorted intervals-list existing)
  "Insert INTERVALS-LIST into EXISTING, maintaining sorted order by start position."
  (if (null? existing)
      intervals-list
      (if (null? intervals-list)
          existing
          (let ((new-start (interval-start (car intervals-list)))
                (existing-start (interval-start (car existing))))
            (if (<= new-start existing-start)
                (append intervals-list existing)
                (cons (car existing)
                      (insert-sorted intervals-list (cdr existing))))))))

;;; Property Search Functions (Phase 5)

(define (text-property-any start end prop value obj)
  "Check if any character in range [START, END) has PROP set to VALUE in OBJ.
Returns the position of first match, or #nil if no match found."
  (let ((intervals (cond
                    ((emacs-string? obj) (emacs-string-intervals obj))
                    ((string? obj) '())
                    (else (buffer-intervals-get obj)))))

    (if (null? intervals)
        #nil
        (let loop ((ints intervals))
          (cond
            ((null? ints) #nil)
            (else
             (let* ((int (car ints))
                    (int-start (interval-start int))
                    (int-end (interval-end int))
                    (int-val (plist-get (interval-plist int) prop)))

               (cond
                 ;; Interval before range - skip
                 ((<= int-end start)
                  (loop (cdr ints)))

                 ;; Interval after range - done
                 ((>= int-start end)
                  #nil)

                 ;; Interval overlaps and value matches
                 ((equal? int-val value)
                  ;; Return first position in overlap
                  (max int-start start))

                 ;; Interval overlaps but value doesn't match
                 (else
                  (loop (cdr ints)))))))))))

(define (text-property-not-all start end prop value obj)
  "Check if any character in range [START, END) has PROP NOT set to VALUE in OBJ.
Returns the position of first mismatch, or #nil if all match."
  (let ((intervals (cond
                    ((emacs-string? obj) (emacs-string-intervals obj))
                    ((string? obj) '())
                    (else (buffer-intervals-get obj)))))

    (if (null? intervals)
        ;; No intervals means no properties, so if value is not #nil, return start
        (if (eq? value #nil)
            #nil
            start)
        (let loop ((ints intervals) (pos start))
          (cond
            ;; Reached end of range
            ((>= pos end) #nil)

            ;; No more intervals
            ((null? ints)
             ;; Check if remaining range has value=#nil
             (if (eq? value #nil)
                 #nil
                 pos))

            (else
             (let* ((int (car ints))
                    (int-start (interval-start int))
                    (int-end (interval-end int))
                    (int-val (plist-get (interval-plist int) prop)))

               (cond
                 ;; Gap before this interval (property=#nil in gap)
                 ((< pos int-start)
                  (if (eq? value #nil)
                      (loop ints int-start)  ; Skip gap, it matches
                      pos))  ; Gap doesn't match, return position

                 ;; We're in this interval
                 ((and (>= pos int-start) (< pos int-end))
                  (if (equal? int-val value)
                      ;; Value matches, continue at end of interval
                      (loop (cdr ints) int-end)
                      ;; Value doesn't match, return position
                      pos))

                 ;; Interval is before pos (shouldn't happen with sorted intervals)
                 ((<= int-end pos)
                  (loop (cdr ints) pos))))))))))

;;; Buffer Modification Hooks
;;
;; These functions are called from C when buffer content changes

(define (buffer-on-insert buffer pos len)
  "Hook called after inserting LEN characters at POS in BUFFER.
Adjusts text property intervals accordingly."
  (let* ((old-intervals (buffer-intervals-get buffer))
         (new-intervals (adjust-intervals-on-insert old-intervals pos len)))
    (buffer-intervals-set! buffer new-intervals)))

(define (buffer-on-delete buffer start end)
  "Hook called after deleting text from START to END in BUFFER.
Adjusts text property intervals accordingly."
  (let* ((old-intervals (buffer-intervals-get buffer))
         (new-intervals (adjust-intervals-on-delete old-intervals start end)))
    (buffer-intervals-set! buffer new-intervals)))

;;; Module initialization

(format #t "~%;; text-properties.scm loaded (wrapper-based)~%")
