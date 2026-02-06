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

;; Character accessors for bolp/eolp.
(define %char-before-fn #f)
(define (char-before-fn)
  (or %char-before-fn
      (let ((fn (symbol-function 'char-before)))
        (set! %char-before-fn fn) fn)))

(define %char-after-fn #f)
(define (char-after-fn)
  (or %char-after-fn
      (let ((fn (symbol-function 'char-after)))
        (set! %char-after-fn fn) fn)))

(define (elisp-bolp)
  "Return t if point is at the beginning of a line."
  (if (or (eq? #t (elisp-bobp))
          (eqv? ((char-before-fn)) 10))  ; 10 = newline character code
      #t
      #nil))

(define (elisp-eolp)
  "Return t if point is at the end of a line.
`End of a line' includes point being at the end of the buffer."
  (if (or (eq? #t (elisp-eobp))
          (eqv? ((char-after-fn)) 10))  ; 10 = newline character code
      #t
      #nil))

(define (elisp-following-char)
  "Return the character following point, as a number.
At the end of the buffer or accessible region, return 0."
  (let ((c ((char-after-fn))))
    (if (eq? c #nil) 0 c)))

(define (elisp-preceding-char)
  "Return the character preceding point, as a number.
At the beginning of the buffer or accessible region, return 0."
  (let ((c ((char-before-fn))))
    (if (eq? c #nil) 0 c)))

;; Modiff accessors for buffer-modified-p.
(define %buffer-modified-tick-fn #f)
(define (buffer-modified-tick-fn)
  (or %buffer-modified-tick-fn
      (let ((fn (symbol-function 'buffer-modified-tick)))
        (set! %buffer-modified-tick-fn fn) fn)))

(define %buffer-save-modiff-fn #f)
(define (buffer-save-modiff-fn)
  (or %buffer-save-modiff-fn
      (let ((fn (symbol-function 'buffer-save-modiff)))
        (set! %buffer-save-modiff-fn fn) fn)))

(define %buffer-autosave-modiff-fn #f)
(define (buffer-autosave-modiff-fn)
  (or %buffer-autosave-modiff-fn
      (let ((fn (symbol-function 'buffer-autosave-modiff)))
        (set! %buffer-autosave-modiff-fn fn) fn)))

(define (elisp-buffer-modified-p . args)
  "Return non-nil if BUFFER was modified since its file was last read or saved.
No argument or nil as argument means use current buffer as BUFFER.
If BUFFER was autosaved since it was last modified, return `autosaved'."
  (let* ((buf (if (null? args) #nil (car args)))
         (save-modiff ((buffer-save-modiff-fn) buf))
         (modiff ((buffer-modified-tick-fn) buf)))
    (if (< save-modiff modiff)
        ;; Buffer is modified - check if autosaved
        (if (= ((buffer-autosave-modiff-fn) buf) modiff)
            'autosaved
            #t)
        #nil)))

;; Cached function handles for set-buffer-modified-p.
(define %restore-buffer-modified-p-fn #f)
(define (restore-buffer-modified-p-fn)
  (or %restore-buffer-modified-p-fn
      (let ((fn (symbol-function 'restore-buffer-modified-p)))
        (set! %restore-buffer-modified-p-fn fn) fn)))

(define %force-mode-line-update-fn #f)
(define (force-mode-line-update-fn)
  (or %force-mode-line-update-fn
      (let ((fn (symbol-function 'force-mode-line-update)))
        (set! %force-mode-line-update-fn fn) fn)))

(define (elisp-set-buffer-modified-p flag)
  "Mark current buffer as modified or unmodified according to FLAG.
A non-nil FLAG means mark the buffer modified.
In addition, this function unconditionally forces redisplay of the
mode lines of the windows that display the current buffer, and also
locks or unlocks the file visited by the buffer, depending on whether
the function's argument is non-nil, but only if both `buffer-file-name'
and `buffer-file-truename' are non-nil."
  ((restore-buffer-modified-p-fn) flag)
  ((force-mode-line-update-fn) #nil))

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
;;; Tier 5 -- Region functions (Phase 6)
;;; ----------------------------------------------------------------

;; Cached function handles for region functions.
(define %marker-position-fn #f)
(define (marker-position-fn)
  (or %marker-position-fn
      (let ((fn (symbol-function 'marker-position)))
        (set! %marker-position-fn fn) fn)))

(define %signal-fn #f)
(define (signal-fn)
  (or %signal-fn
      (let ((fn (symbol-function 'signal)))
        (set! %signal-fn fn) fn)))

;; Helper to get the region limit (beginning or end).
;; BEGINNINGP is #t for region-beginning, #f for region-end.
(define (region-limit beginningp)
  (let ((transient-mark-mode (symbol-value 'transient-mark-mode))
        (mark-even-if-inactive (symbol-value 'mark-even-if-inactive))
        (mark-active (symbol-value 'mark-active)))
    ;; Check if mark is inactive when it should be active.
    (when (and (not (eq? transient-mark-mode #nil))
               (eq? mark-even-if-inactive #nil)
               (eq? mark-active #nil))
      ((signal-fn) 'mark-inactive #nil))
    ;; Get mark position.
    (let ((m ((marker-position-fn) (elisp-mark-marker))))
      (when (eq? m #nil)
        (error "The mark is not set now, so there is no region"))
      ;; Clip mark to current narrowing and compare with point.
      (let* ((pt ((point-fn)))
             (pt-min ((point-min-fn)))
             (pt-max ((point-max-fn)))
             (clipped-m (max pt-min (min m pt-max))))
        (if beginningp
            (min pt clipped-m)
            (max pt clipped-m))))))

(define (elisp-region-beginning)
  "Return the integer value of point or mark, whichever is smaller."
  (region-limit #t))

(define (elisp-region-end)
  "Return the integer value of point or mark, whichever is larger."
  (region-limit #f))

;;; ----------------------------------------------------------------
;;; Tier 6 -- Undo functions (Phase 7)
;;; ----------------------------------------------------------------

;; Cached function handles for undo functions.
(define %get-buffer-fn #f)
(define (get-buffer-fn)
  (or %get-buffer-fn
      (let ((fn (symbol-function 'get-buffer)))
        (set! %get-buffer-fn fn) fn)))

(define (elisp-buffer-enable-undo . args)
  "Start keeping undo information for buffer BUFFER.
No argument or nil as argument means do this for the current buffer."
  (let* ((buffer-arg (if (null? args) #nil (car args)))
         (buf (if (eq? buffer-arg #nil)
                  #nil  ; current buffer
                  (let ((found ((get-buffer-fn) buffer-arg)))
                    (if (eq? found #nil)
                        (error "No such buffer: %s" buffer-arg)
                        found)))))
    ;; Get the undo-list from the buffer's hash
    (let ((undo-list (buf-hash-ref buf 'buffer-undo-list)))
      ;; If undo is disabled (undo-list is t), enable it by setting to nil
      ;; Check for both Emacs t symbol and Scheme #t
      (when (or (eq? undo-list #t) (eq? undo-list 't))
        ;; hashq-set! on the buffer's hash
        (let ((h (buf-hash buf)))
          (when (not (eq? h #nil))
            (hashq-set! h 'buffer-undo-list #nil)))))
    #nil))

;;; ----------------------------------------------------------------
;;; Tier 7 -- File I/O functions (Phase 8)
;;; ----------------------------------------------------------------

(define (elisp-recent-auto-save-p)
  "Return t if current buffer has been auto-saved recently.
More precisely, if it has been auto-saved since last read from or saved
in the visited file.  If the buffer has no visited file,
then any auto-save counts as \"recent\"."
  ;; SAVE_MODIFF < BUF_AUTOSAVE_MODIFF means we've autosaved since last save.
  ;; Note: buffer-save-modiff with no arg returns SAVE_MODIFF for current buffer.
  ;; Note: buffer-autosave-modiff with no arg returns BUF_AUTOSAVE_MODIFF for current buffer.
  (if (< ((buffer-save-modiff-fn)) ((buffer-autosave-modiff-fn)))
      #t
      #nil))

(define (elisp-car-less-than-car a b)
  "Return t if (car A) is numerically less than (car B)."
  (if (< (car a) (car b)) #t #nil))

;;; ----------------------------------------------------------------
;;; Registration
;;; ----------------------------------------------------------------

(define (init-buffer-locals-registrations)
  "Register Scheme buffer accessor functions, replacing C DEFUNs."
  ;; Register Scheme replacements.
  (for-each (lambda (sym-fun)
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
              (bolp ,elisp-bolp)
              (eolp ,elisp-eolp)
              (following-char ,elisp-following-char)
              (preceding-char ,elisp-preceding-char)
              (buffer-modified-p ,elisp-buffer-modified-p)
              (set-buffer-modified-p ,elisp-set-buffer-modified-p)
              (get-file-buffer ,elisp-get-file-buffer)
              (get-truename-buffer ,elisp-get-truename-buffer)
              (find-buffer ,elisp-find-buffer)
              (region-beginning ,elisp-region-beginning)
              (region-end ,elisp-region-end)
              (buffer-enable-undo ,elisp-buffer-enable-undo)
              (recent-auto-save-p ,elisp-recent-auto-save-p)
              (car-less-than-car ,elisp-car-less-than-car))))
