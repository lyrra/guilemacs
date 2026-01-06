;;; Guilemacs Lisp
;;;
;;; Text Properties System - Unified Module
;;;
;;; This module consolidates the text property system into a single coherent unit.
;;; Previously split across intervals.scm, emacs-string.scm, text-properties.scm,
;;; and string-operations.scm, now unified for clarity and maintainability.
;;;
;;; ARCHITECTURE:
;;; 1. Interval Tree Data Structure - non-overlapping ranges with plists
;;; 2. Emacs-String Wrapper - pairs string content with interval list
;;; 3. Text Property Operations - high-level API (propertize, get-text-property, etc.)
;;; 4. Wrapper-Aware String Operations - substring, concat preserving properties
;;; 5. Buffer Property Storage - hash table for buffer text properties
;;;
;;; KEY INSIGHTS:
;;; - Intervals are NON-OVERLAPPING and partition the text
;;; - Adjacent intervals with identical properties are automatically merged
;;; - String wrappers solve the identity problem (strings lack stable identity)
;;; - Buffers have stable identity, so hash table storage is safe
;;;

;;;
;;; SECTION 1: MODULE SETUP
;;;
;;; This module is properly declared as (language elisp emacs text-properties).
;;; C code accesses these functions via scm_c_resolve_module and scm_c_public_ref.
;;;

(define-module (language elisp emacs text-properties)
  #:use-module (srfi srfi-9)    ; define-record-type
  #:use-module (srfi srfi-1)    ; list utilities (for 'any')
  #:use-module (ice-9 format)
  #:use-module (srfi srfi-9 gnu)  ; set-record-type-printer!
  #:export (
    ;; Record types and predicates
    interval? emacs-string? emacs-string-predicate

    ;; String wrapper operations
    make-emacs-string emacs-string-content emacs-string-intervals
    emacs-string-length wrap-string unwrap-string has-properties?
    deep-unwrap-for-printing emacs-string-equal emacs-string-intervals-runtime

    ;; Text property operations
    propertize get-text-property text-properties-at
    add-text-properties put-text-property
    remove-text-properties set-text-properties

    ;; Property search
    text-property-any text-property-not-all
    next-property-change previous-property-change
    next-single-property-change previous-single-property-change

    ;; Wrapper-aware string operations
    substring-with-properties concat-with-properties
    upcase-with-properties downcase-with-properties

    ;; Buffer property operations
    buffer-intervals-get buffer-intervals-set!
    buffer-add-text-properties buffer-put-text-property
    buffer-get-text-property buffer-text-properties-at
    buffer-on-insert buffer-on-delete

    ;; Internal utilities (for C bridge)
    get-interval-start get-interval-end get-interval-plist
    merge-intervals-concat))

;;;
;;; SECTION 2: INTERVAL DATA STRUCTURE
;;;
;;; Intervals represent contiguous ranges of text with associated properties.
;;; They form a non-overlapping partition of the text.
;;;

(define-record-type <interval>
  (make-interval start end plist)
  interval?
  (start interval-start interval-start-set!)
  (end interval-end interval-end-set!)
  (plist interval-plist interval-plist-set!))

;;;
;;; SECTION 3: PROPERTY LIST OPERATIONS
;;;
;;; Plists are stored as flat lists: (key1 val1 key2 val2 ...)
;;;

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
  "Return #t if property lists P1 and P2 are equal.
Uses eq? for value comparison to match Emacs behavior - intervals
should only merge when property values are the exact same object,
not just structurally equal.  This is critical for display properties
where each cell needs its own image object."
  (and (= (length p1) (length p2))
       (let loop ((lst p1))
         (or (null? lst)
             (and (eq? (plist-get p2 (car lst)) (cadr lst))
                  (loop (cddr lst)))))))

(define (parse-plist props)
  "Parse property list from list of alternating keys and values.
Example: '(face bold mouse-face highlight) -> same list
Validates that length is even."
  (when (odd? (length props))
    (error "parse-plist: property list must have even length" props))
  props)

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

;;;
;;; SECTION 4: INTERVAL SEARCH OPERATIONS
;;;

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

;;;
;;; SECTION 5: INTERVAL MANIPULATION
;;;

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
      ;; Track last covered position to handle gaps
      (let loop ((ints intervals) (result '()) (last-covered start))
        (cond
          ((null? ints)
           ;; Done processing - add final gap if needed
           (if (< last-covered end)
               (merge-adjacent-intervals (reverse (cons (make-interval last-covered end new-props) result)))
               (merge-adjacent-intervals (reverse result))))

          ((>= (interval-start (car ints)) end)
           ;; This interval is after our range
           ;; Add any remaining gap, then keep rest as-is
           (if (< last-covered end)
               (merge-adjacent-intervals (append (reverse (cons (make-interval last-covered end new-props) result)) ints))
               (merge-adjacent-intervals (append (reverse result) ints))))

          ((<= (interval-end (car ints)) start)
           ;; This interval is before our range (or adjacent), keep it
           (loop (cdr ints) (cons (car ints) result) last-covered))

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

             ;; Handle gap before this interval (if any)
             (define gap-part
               (if (< last-covered (max int-start start))
                   (list (make-interval last-covered (max int-start start) new-props))
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
             ;; Update last-covered to end of overlap
             (loop (cdr ints)
                   (append after-part overlap-part gap-part before-part result)
                   overlap-end)))))))

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

;;;
;;; SECTION 6: BUFFER MODIFICATION HOOKS
;;;

(define (adjust-intervals-on-insert intervals pos length)
  "Adjust INTERVALS after inserting LENGTH characters at POS.
All intervals at or after POS are shifted right by LENGTH.
Returns new interval list."
  (if (null? intervals)
      '()
      (let loop ((ints intervals) (result '()))
        (cond
          ((null? ints)
           (merge-adjacent-intervals (reverse result)))

          (else
           (let* ((int (car ints))
                  (int-start (interval-start int))
                  (int-end (interval-end int))
                  (int-plist (interval-plist int)))

             (cond
               ;; Interval completely before insertion - keep as-is
               ((<= int-end pos)
                (loop (cdr ints) (cons int result)))

               ;; Interval completely after insertion - shift right
               ((>= int-start pos)
                (loop (cdr ints)
                      (cons (make-interval (+ int-start length)
                                          (+ int-end length)
                                          int-plist)
                            result)))

               ;; Insertion is inside interval - split and expand
               (else
                ;; Create single expanded interval covering insertion
                (loop (cdr ints)
                      (cons (make-interval int-start
                                          (+ int-end length)
                                          int-plist)
                            result))))))))))

(define (adjust-intervals-on-delete intervals start end)
  "Adjust INTERVALS after deleting text from START to END.
Intervals in the deleted range are removed/clipped.
Intervals after END are shifted left by (END - START).
Returns new interval list."
  (if (null? intervals)
      '()
      (let ((delete-len (- end start)))
        (let loop ((ints intervals) (result '()))
          (cond
            ((null? ints)
             (merge-adjacent-intervals (reverse result)))

            (else
             (let* ((int (car ints))
                    (int-start (interval-start int))
                    (int-end (interval-end int))
                    (int-plist (interval-plist int)))

               (cond
                 ;; Interval completely before deletion - keep as-is
                 ((<= int-end start)
                  (loop (cdr ints) (cons int result)))

                 ;; Interval completely after deletion - shift left
                 ((>= int-start end)
                  (loop (cdr ints)
                        (cons (make-interval (- int-start delete-len)
                                            (- int-end delete-len)
                                            int-plist)
                              result)))

                 ;; Interval completely inside deletion - remove it
                 ((and (>= int-start start) (<= int-end end))
                  (loop (cdr ints) result))

                 ;; Deletion inside interval - shrink it
                 ((and (<= int-start start) (>= int-end end))
                  (loop (cdr ints)
                        (cons (make-interval int-start
                                            (- int-end delete-len)
                                            int-plist)
                              result)))

                 ;; Interval starts before, ends inside deletion - clip end
                 ((< int-start start)
                  (loop (cdr ints)
                        (cons (make-interval int-start start int-plist)
                              result)))

                 ;; Interval starts inside deletion, ends after - clip start and shift
                 (else
                  (loop (cdr ints)
                        (cons (make-interval start
                                            (- int-end delete-len)
                                            int-plist)
                              result)))))))))))

;;;
;;; SECTION 7: C BRIDGE ACCESSORS
;;;
;;; Record accessors are syntax transformers, not procedures.
;;; These wrapper functions allow C code to call them.
;;;

(define (get-interval-start interval)
  "Get the start position of INTERVAL (for C bridge)."
  (interval-start interval))

(define (get-interval-end interval)
  "Get the end position of INTERVAL (for C bridge)."
  (interval-end interval))

(define (get-interval-plist interval)
  "Get the property list of INTERVAL (for C bridge)."
  (interval-plist interval))

;;;
;;; SECTION 8: EMACS-STRING WRAPPER
;;;
;;; The wrapper pairs string content with interval list.
;;; This solves the string identity problem for text properties.
;;;

(define-record-type <emacs-string>
  (%make-emacs-string content intervals)
  emacs-string?
  (content %emacs-string-content)
  (intervals emacs-string-intervals emacs-string-intervals-set!))

;;; Install custom printer for emacs-string records
;;; This makes emacs-strings transparent in error messages and backtraces
;;; Without this, Guile's error formatter tries to string-append the record fields, which fails
;;; Use 'write' to properly quote the string content
(set-record-type-printer! <emacs-string>
  (lambda (record port)
    (write (%emacs-string-content record) port)))

;;; Runtime-callable predicate for C code
(define (emacs-string-predicate obj)
  "Runtime-callable wrapper for emacs-string? predicate.
This is needed because C code can't call macros directly."
  (emacs-string? obj))

;;; Runtime-callable accessor for C code
(define (emacs-string-intervals-runtime obj)
  "Runtime-callable wrapper for emacs-string-intervals accessor.
This is needed because SRFI-9 accessors are syntax transformers, not procedures."
  (emacs-string-intervals obj))

;;;
;;; SECTION 9: WRAPPER CONSTRUCTORS & ACCESSORS
;;;

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

;;;
;;; SECTION 10: WRAPPER UTILITIES
;;;

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

(define (emacs-string-equal obj1 obj2)
  "Custom equal comparison that treats emacs-string wrappers transparently.
Compares wrapper content, ignoring text properties, but preserves list/vector structure.
This is called by the C `equal` function."
  (cond
    ;; Both are wrappers - compare content
    ((and (emacs-string? obj1) (emacs-string? obj2))
     (string=? (%emacs-string-content obj1) (%emacs-string-content obj2)))

    ;; One is wrapper, one is plain string - compare content
    ((and (emacs-string? obj1) (string? obj2))
     (string=? (%emacs-string-content obj1) obj2))
    ((and (string? obj1) (emacs-string? obj2))
     (string=? obj1 (%emacs-string-content obj2)))

    ;; Both are lists - compare recursively
    ((and (pair? obj1) (pair? obj2))
     (and (emacs-string-equal (car obj1) (car obj2))
          (emacs-string-equal (cdr obj1) (cdr obj2))))

    ;; Both are vectors - compare recursively
    ((and (vector? obj1) (vector? obj2))
     (and (= (vector-length obj1) (vector-length obj2))
          (let loop ((i 0))
            (or (>= i (vector-length obj1))
                (and (emacs-string-equal (vector-ref obj1 i) (vector-ref obj2 i))
                     (loop (+ i 1)))))))

    ;; For everything else, use Guile's equal?
    (else
     (equal? obj1 obj2))))

(define (has-properties? obj)
  "Return #t if OBJ is an emacs-string with non-empty intervals.
Plain strings always return #f."
  (and (emacs-string? obj)
       (not (null? (emacs-string-intervals obj)))))

;;;
;;; SECTION 11: BUFFER PROPERTY STORAGE
;;;
;;; Buffers have stable identity, so hash table is safe for them.
;;;

(define *buffer-text-properties* (make-hash-table))

(define (buffer-intervals-get buffer)
  "Get interval list for BUFFER."
  (hashq-ref *buffer-text-properties* buffer '()))

(define (buffer-intervals-set! buffer intervals)
  "Set interval list for BUFFER."
  (if (null? intervals)
      (hashq-remove! *buffer-text-properties* buffer)
      (hashq-set! *buffer-text-properties* buffer intervals)))

;;;
;;; SECTION 12: TEXT PROPERTY OPERATIONS
;;;

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

    ;; Plain string - wrap it first, then add properties
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

;;;
;;; SECTION 13: BUFFER-SPECIFIC ALIASES
;;;

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

;;;
;;; SECTION 14: PROPERTY REMOVAL AND SETTING
;;;

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

                 ;; Interval completely after range - store and return
                 ((>= int-start end)
                  (let ((new-intervals (merge-adjacent-intervals (append (reverse result) ints))))
                    (cond
                      ((emacs-string? obj)
                       (emacs-string-intervals-set! obj new-intervals)
                       removed?)
                      ((string? obj) #nil)
                      (else
                       (buffer-intervals-set! obj new-intervals)
                       removed?))))

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
                         ;; props is a plist (prop val prop val ...), step by 2
                         (new-plist (let remove-loop ((plist int-plist) (props-to-remove props))
                                     (if (null? props-to-remove)
                                         plist
                                         (let ((without-prop (remove-from-plist plist (car props-to-remove))))
                                           (when (not (equal? plist without-prop))
                                             (set! removed? #t))
                                           (remove-loop without-prop (if (null? (cdr props-to-remove))
                                                                         '()
                                                                         (cddr props-to-remove)))))))
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

             ;; Interval completely after range - add new interval and store
             ((>= int-start end)
              (let* ((cleared (reverse result))
                     (new-interval (if (null? props)
                                      '()
                                      (list (make-interval start end props))))
                     (merged (merge-adjacent-intervals
                              (if (null? new-interval)
                                  (append cleared ints)
                                  (insert-sorted new-interval (append cleared ints))))))
                (cond
                  ((emacs-string? obj)
                   (emacs-string-intervals-set! obj merged))
                  ((string? obj) #f)
                  (else
                   (buffer-intervals-set! obj merged)))
                #t))

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

;;;
;;; SECTION 15: PROPERTY CHANGE SEARCH
;;;
;;; Functions to find positions where text properties change.
;;;

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

               ;; We're before this interval
               ((< position int-start)
                (if (and actual-limit (>= int-start actual-limit))
                    (or limit #nil)
                    int-start))

               ;; We're inside this interval
               ((< position int-end)
                (if (and actual-limit (>= int-end actual-limit))
                    (or limit #nil)
                    int-end))

               (else
                (loop (cdr ints)))))))))))

(define (previous-property-change position object limit)
  "Find previous position where ANY property changes in OBJECT before POSITION.
Returns the position of the change, or LIMIT if no change found."
  (let* ((intervals (cond
                     ((emacs-string? object) (emacs-string-intervals object))
                     ((string? object) '())
                     (else (buffer-intervals-get object))))
         (actual-limit (if (and limit (not (eq? limit #nil))) limit 0)))

    (if (null? intervals)
        (or limit #nil)
        (let loop ((ints (reverse intervals)))
          (cond
           ((null? ints) (or limit #nil))
           (else
            (let* ((int (car ints))
                   (int-start (interval-start int))
                   (int-end (interval-end int)))
              (cond
               ((>= int-start position) (loop (cdr ints)))
               ((> position int-end)
                (if (<= int-end actual-limit) (or limit #nil) int-end))
               ((>= position int-start)
                (if (<= int-start actual-limit) (or limit #nil) int-start))
               (else (loop (cdr ints)))))))))))

(define (next-single-property-change position prop obj limit)
  "Find next position where PROP changes in OBJ starting from POSITION."
  (let* ((intervals (cond
                     ((emacs-string? obj) (emacs-string-intervals obj))
                     ((string? obj) '())
                     (else (buffer-intervals-get obj))))
         (current-val (interval-get-property-at intervals position prop)))
    (if (null? intervals)
        (or limit #nil)
        ;; We need to track gaps between intervals as we search forward
        ;; Intervals only exist for text WITH properties, gaps have nil properties
        ;; prev-end tracks the END of the previously processed interval
        (let loop ((ints intervals) (prev-end #f))
          (cond
            ((null? ints)
             ;; No more intervals - if current position is inside a non-nil region,
             ;; the property changes to nil at prev-end
             (if (and prev-end
                      (not (eq? current-val #nil)))
                 prev-end
                 (or limit #nil)))

            (else
             (let* ((int (car ints))
                    (int-start (interval-start int))
                    (int-end (interval-end int))
                    (int-val (plist-get (interval-plist int) prop)))
               (cond
                 ;; Interval is completely before position - skip it (update prev-end)
                 ((<= int-end position)
                  (loop (cdr ints) int-end))

                 ;; We're before this interval - check value
                 ((< position int-start)
                  (if (eq? current-val #nil)
                      ;; In nil region, change is at start of interval (if different value)
                      (if (eq? int-val #nil)
                          (loop (cdr ints) int-end)
                          int-start)
                      ;; In non-nil region before any interval - shouldn't normally happen
                      int-start))

                 ;; We're inside this interval
                 ((and (>= position int-start) (< position int-end))
                  (if (equal? int-val current-val)
                      ;; Same value - need to check what comes after this interval
                      ;; If there's a gap or next interval has different value, return int-end
                      ;; Otherwise continue searching
                      (if (null? (cdr ints))
                          ;; No more intervals after this, property changes to nil at int-end
                          (if (eq? current-val #nil)
                              (or limit #nil)
                              int-end)
                          ;; Check next interval
                          (let* ((next-int (cadr ints))
                                 (next-start (interval-start next-int))
                                 (next-val (plist-get (interval-plist next-int) prop)))
                            (if (or (> next-start int-end)  ; Gap after this interval
                                    (not (equal? next-val current-val)))  ; Or different value
                                int-end
                                ;; Next interval is adjacent with same value, keep searching
                                (loop (cdr ints) int-end))))
                      ;; Different value - change is at interval start
                      int-start))

                 (else
                  (loop (cdr ints) int-end))))))))))

(define (previous-single-property-change position prop obj limit)
  "Find previous position where PROP changes in OBJ before POSITION."
  (let* ((intervals (cond
                     ((emacs-string? obj) (emacs-string-intervals obj))
                     ((string? obj) '())
                     (else (buffer-intervals-get obj))))
         (current-val (if (> position 0)
                         (interval-get-property-at intervals (- position 1) prop)
                         #nil)))
    (if (null? intervals)
        (or limit #nil)
        ;; We need to track gaps between intervals as we search backward
        ;; Intervals only exist for text WITH properties, gaps have nil properties
        ;; prev-start tracks the START of the previously processed interval
        (let loop ((ints (reverse intervals)) (prev-start #f))
          (cond
            ((null? ints)
             ;; No more intervals - check if there's a gap at the beginning
             ;; If the first interval doesn't start at 0 and current-val is not nil,
             ;; there's an implicit nil-property region before the first interval
             (if (and (not (null? intervals))
                      (> (interval-start (car intervals)) 0)
                      (not (eq? current-val #nil)))
                 ;; There's a property change at the start of the first interval
                 (interval-start (car intervals))
                 (or limit #nil)))
            (else
             (let* ((int (car ints))
                    (int-start (interval-start int))
                    (int-end (interval-end int))
                    (int-val (plist-get (interval-plist int) prop)))
               (cond
                 ;; Interval at or after position - skip it (don't update prev-start)
                 ((>= int-start position)
                  (loop (cdr ints) prev-start))

                 ;; Check if there's a gap AFTER this interval (before prev-start)
                 ;; The gap has nil properties, so if current-val is not nil, this is a change
                 ((and prev-start
                       (< int-end prev-start)  ; There's a gap between this and previous interval
                       (not (eq? current-val #nil)))  ; And we're searching from a non-nil region
                  ;; Return the position where the gap ends (start of next interval in forward order)
                  prev-start)

                 ;; This interval's value differs from current-val
                 ((not (equal? int-val current-val))
                  (interval-end int))

                 ;; This interval has the same value - continue searching
                 (else
                  (loop (cdr ints) int-start))))))))))

(define (text-property-any start end prop value obj)
  "Check if any character in range [START, END) has PROP set to VALUE."
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
                    (int-val (plist-get (interval-plist int) prop)))
               (cond
                 ((<= (interval-end int) start) (loop (cdr ints)))
                 ((>= (interval-start int) end) #nil)
                 ((equal? int-val value) (max (interval-start int) start))
                 (else (loop (cdr ints)))))))))))

(define (text-property-not-all start end prop value obj)
  "Check if any character in range [START, END) has PROP NOT set to VALUE."
  (let ((intervals (cond
                    ((emacs-string? obj) (emacs-string-intervals obj))
                    ((string? obj) '())
                    (else (buffer-intervals-get obj)))))
    (if (null? intervals)
        (if (eq? value #nil) #nil start)
        (let loop ((ints intervals) (pos start))
          (cond
            ((>= pos end) #nil)
            ((null? ints) (if (eq? value #nil) #nil pos))
            (else
             (let* ((int (car ints))
                    (int-val (plist-get (interval-plist int) prop)))
               (cond
                 ((< pos (interval-start int))
                  (if (eq? value #nil) (loop ints (interval-start int)) pos))
                 ((and (>= pos (interval-start int)) (< pos (interval-end int)))
                  (if (equal? int-val value)
                      (loop (cdr ints) (interval-end int))
                      pos))
                 ((<= (interval-end int) pos) (loop (cdr ints) pos))))))))))

;;;
;;; SECTION 16: WRAPPER-AWARE STRING OPERATIONS
;;;
;;; String operations that preserve text properties.
;;;

;;; Save original Guile string functions
(define %guile-substring substring)
(define %guile-string-append string-append)
(define %guile-string-upcase string-upcase)
(define %guile-string-downcase string-downcase)

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

;;;
;;; Module complete - all functions exported via #:export declaration
;;;
