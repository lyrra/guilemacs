(define-module (emacs buffer-locals)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (init-buffer-locals-registrations))

;;; Phase 5: Scheme replacements for C buffer accessor DEFUNs.
;;;
;;; These functions replace C DEFUNs with pure Scheme code that reads
;;; from the per-buffer hash table via hashq-ref.  DEFVAR_PER_BUFFER
;;; fields use their Lisp symbol as key; internal fields use Scheme
;;; keywords (#:name, #:mark, etc.).

;; Helper: get the hash table for a buffer (nil = current buffer).
(define (buf-hash buf)
  ((buffer-local-hash-fn) buf))

;; Nil-safe hash lookup: returns #nil if hash is nil (killed buffer).
(define (buf-hash-ref buf key)
  (let ((h (buf-hash buf)))
    (if (eq? h #nil) #nil (hashq-ref h key))))

;;; ----------------------------------------------------------------
;;; Tier 1 -- DEFVAR_PER_BUFFER accessor (symbol keys, already in hash)
;;; ----------------------------------------------------------------

(define (elisp-buffer-file-name . args)
  "Return name of file BUFFER is visiting, or nil if none."
  (buf-hash-ref (if (null? args) #nil (car args)) 'buffer-file-name))

;;; ----------------------------------------------------------------
;;; Tier 2 -- Internal field accessors (keyword keys, added in Step 1)
;;; ----------------------------------------------------------------

(define (elisp-buffer-name . args)
  "Return the name of BUFFER, as a string."
  (buf-hash-ref (if (null? args) #nil (car args)) #:name))

(define (elisp-buffer-last-name . args)
  "Return last name of BUFFER, as a string."
  (buf-hash-ref (if (null? args) #nil (car args)) #:last-name))

(define (elisp-mark-marker)
  "Return this buffer's mark, as a marker object."
  (buf-hash-ref #nil #:mark))

(define (elisp-current-local-map)
  "Return current buffer's local keymap, or nil if it has none."
  (buf-hash-ref #nil #:keymap))

(define (elisp-syntax-table)
  "Return the current syntax table."
  (buf-hash-ref #nil #:syntax-table))

(define (elisp-category-table)
  "Return the current category table."
  (buf-hash-ref #nil #:category-table))

(define (elisp-current-case-table)
  "Return the case table of the current buffer."
  (buf-hash-ref #nil #:downcase-table))

;;; ----------------------------------------------------------------
;;; Tier 3 -- Derived functions (call existing C DEFUNs)
;;; ----------------------------------------------------------------

;; Lazily-cached C function handles (same pattern as buffer-local-hash-fn).
(define %point-fn #f)
(define %point-min-fn #f)
(define %point-max-fn #f)

(define (point-fn)
  (or %point-fn
      (let ((fn (symbol-function 'point)))
        (set! %point-fn fn) fn)))

(define (point-min-fn)
  (or %point-min-fn
      (let ((fn (symbol-function 'point-min)))
        (set! %point-min-fn fn) fn)))

(define (point-max-fn)
  (or %point-max-fn
      (let ((fn (symbol-function 'point-max)))
        (set! %point-max-fn fn) fn)))

(define (elisp-bobp)
  "Return t if point is at the beginning of the buffer."
  (if (= ((point-fn)) ((point-min-fn))) #t #nil))

(define (elisp-eobp)
  "Return t if point is at the end of the buffer."
  (if (= ((point-fn)) ((point-max-fn))) #t #nil))

;;; ----------------------------------------------------------------
;;; Tier 4 -- Buffer-list iteration functions
;;; ----------------------------------------------------------------

;; Lazily-cached function handles for buffer iteration helpers.
(define %buffer-list-fn #f)
(define (buffer-list-fn)
  (or %buffer-list-fn
      (let ((fn (symbol-function 'buffer-list)))
        (set! %buffer-list-fn fn) fn)))

(define %expand-file-name-fn #f)
(define (expand-file-name-fn)
  (or %expand-file-name-fn
      (let ((fn (symbol-function 'expand-file-name)))
        (set! %expand-file-name-fn fn) fn)))

(define %find-file-name-handler-fn #f)
(define (find-file-name-handler-fn)
  (or %find-file-name-handler-fn
      (let ((fn (symbol-function 'find-file-name-handler)))
        (set! %find-file-name-handler-fn fn) fn)))

(define %string-equal-fn #f)
(define (string-equal-fn)
  (or %string-equal-fn
      (let ((fn (symbol-function 'string-equal)))
        (set! %string-equal-fn fn) fn)))

(define %bufferp-fn #f)
(define (bufferp-fn)
  (or %bufferp-fn
      (let ((fn (symbol-function 'bufferp)))
        (set! %bufferp-fn fn) fn)))

(define %buffer-local-value-fn #f)
(define (buffer-local-value-fn)
  (or %buffer-local-value-fn
      (let ((fn (symbol-function 'buffer-local-value)))
        (set! %buffer-local-value-fn fn) fn)))

(define %equal-fn #f)
(define (equal-fn)
  (or %equal-fn
      (let ((fn (symbol-function 'equal)))
        (set! %equal-fn fn) fn)))

(define (elisp-get-file-buffer filename)
  "Return the buffer visiting file FILENAME (a string).
The buffer's `buffer-file-name' must match exactly the expansion of FILENAME.
If there is no such live buffer, return nil.
See also `find-buffer-visiting'."
  (let* ((expanded ((expand-file-name-fn) filename))
         (handler ((find-file-name-handler-fn) expanded 'get-file-buffer)))
    (if (not (eq? handler #nil))
        ;; Delegate to file name handler.
        (let ((result (handler 'get-file-buffer expanded)))
          (if (not (eq? ((bufferp-fn) result) #nil)) result #nil))
        ;; Loop over live buffers comparing buffer-file-name.
        (let loop ((bufs ((buffer-list-fn))))
          (if (null? bufs) #nil
              (let* ((buf (car bufs))
                     (fname (buf-hash-ref buf 'buffer-file-name)))
                (if (and (string? fname)
                         (not (eq? ((string-equal-fn) fname expanded) #nil)))
                    buf
                    (loop (cdr bufs)))))))))

(define (elisp-get-truename-buffer filename)
  "Return the buffer with `file-truename' equal to FILENAME (a string).
If there is no such live buffer, return nil.
See also `find-buffer-visiting'."
  (let loop ((bufs ((buffer-list-fn))))
    (if (null? bufs) #nil
        (let* ((buf (car bufs))
               (truename (buf-hash-ref buf 'buffer-file-truename)))
          (if (and (string? truename)
                   (not (eq? ((string-equal-fn) truename filename) #nil)))
              buf
              (loop (cdr bufs)))))))

(define (elisp-find-buffer variable value)
  "Return the buffer with buffer-local VARIABLE `equal' to VALUE.
If there is no such live buffer, return nil.
See also `find-buffer-visiting'."
  (let loop ((bufs ((buffer-list-fn))))
    (if (null? bufs) #nil
        (let* ((buf (car bufs))
               (bval ((buffer-local-value-fn) variable buf)))
          (if (not (eq? ((equal-fn) value bval) #nil))
              buf
              (loop (cdr bufs)))))))

;;; ----------------------------------------------------------------
;;; Registration
;;; ----------------------------------------------------------------

(define (init-buffer-locals-registrations)
  "Register Scheme buffer accessor functions, replacing C DEFUNs."
  ;; Register Scheme replacements.
  (for-each (lambda (sym-fun)
              (format (current-error-port) "-- registering ~s~%" sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `((buffer-file-name ,elisp-buffer-file-name)
              (buffer-name ,elisp-buffer-name)
              (buffer-last-name ,elisp-buffer-last-name)
              (mark-marker ,elisp-mark-marker)
              (current-local-map ,elisp-current-local-map)
              (syntax-table ,elisp-syntax-table)
              (category-table ,elisp-category-table)
              (current-case-table ,elisp-current-case-table)
              (bobp ,elisp-bobp)
              (eobp ,elisp-eobp)
              (get-file-buffer ,elisp-get-file-buffer)
              (get-truename-buffer ,elisp-get-truename-buffer)
              (find-buffer ,elisp-find-buffer))))
