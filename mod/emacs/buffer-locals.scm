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

;;; ----------------------------------------------------------------
;;; Tier 1 -- DEFVAR_PER_BUFFER accessor (symbol keys, already in hash)
;;; ----------------------------------------------------------------

(define (elisp-buffer-file-name . args)
  "Return name of file BUFFER is visiting, or nil if none."
  (hashq-ref (buf-hash (if (null? args) #nil (car args)))
             'buffer-file-name))

;;; ----------------------------------------------------------------
;;; Tier 2 -- Internal field accessors (keyword keys, added in Step 1)
;;; ----------------------------------------------------------------

(define (elisp-buffer-name . args)
  "Return the name of BUFFER, as a string."
  (hashq-ref (buf-hash (if (null? args) #nil (car args)))
             #:name))

(define (elisp-buffer-last-name . args)
  "Return last name of BUFFER, as a string."
  (hashq-ref (buf-hash (if (null? args) #nil (car args)))
             #:last-name))

(define (elisp-mark-marker)
  "Return this buffer's mark, as a marker object."
  (hashq-ref (buf-hash #nil) #:mark))

;;; ----------------------------------------------------------------
;;; Tier 3 -- Derived functions (call existing C DEFUNs)
;;; ----------------------------------------------------------------

;; Cached C function handles, set during init.
(define %point-fn #f)
(define %point-min-fn #f)
(define %point-max-fn #f)

(define (elisp-bobp)
  "Return t if point is at the beginning of the buffer."
  (if (= (%point-fn) (%point-min-fn)) #t #nil))

(define (elisp-eobp)
  "Return t if point is at the end of the buffer."
  (if (= (%point-fn) (%point-max-fn)) #t #nil))

;;; ----------------------------------------------------------------
;;; Registration
;;; ----------------------------------------------------------------

(define (init-buffer-locals-registrations)
  "Register Scheme buffer accessor functions, replacing C DEFUNs."
  ;; Cache C function handles for derived functions.
  (set! %point-fn (symbol-function 'point))
  (set! %point-min-fn (symbol-function 'point-min))
  (set! %point-max-fn (symbol-function 'point-max))
  ;; Register Scheme replacements.
  (for-each (lambda (sym-fun)
              (format (current-error-port) "-- registering ~s~%" sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `((buffer-file-name ,elisp-buffer-file-name)
              (buffer-name ,elisp-buffer-name)
              (buffer-last-name ,elisp-buffer-last-name)
              (mark-marker ,elisp-mark-marker)
              (bobp ,elisp-bobp)
              (eobp ,elisp-eobp))))
