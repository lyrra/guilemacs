;;; image.scm --- the image file resolution and handle policy of
;;;               src/image.c  ((emacs image))
;;;
;;; M51 imp-4 moves the image file HANDLE from C to Scheme.  Scheme
;;; resolves the image path, opens the file as a Guile port, reads the
;;; bytes, and closes the port.  C decodes the bytes.  C keeps the image
;;; cache, struct image, the pixmaps, and the decoders.
;;;
;;;   (image-resolve-path filename) -> the resolved path string, or #f.
;;;        Search data-directory/images (through expand-file-name) first,
;;;        then x-bitmap-file-path.  Use this order only; it matches
;;;        image_find_image_fd (src/image.c).
;;;   (image-open path)             -> a Guile port open for binary
;;;        read, or #f.  Scheme opens with open-fdes plus fdopen.
;;;   (image-handle-read port n)    -> a bytevector of at most N bytes,
;;;        or #f at EOF.  Retries EINTR and EAGAIN here.
;;;   (image-close port)            -> close the port.
;;;   (image-read-file filename)    -> a bytevector of all bytes, or #f.
;;;        The whole-bytes entry: resolve, open, read to EOF, and close
;;;        in a dynamic-wind.  The port never crosses to C.
;;;
;;; Every value is plain: a string, a bytevector, a port, or #f.  No
;;; Lisp_Object, no pathname char *, no struct image, and no
;;; Emacs_Pix_Container crosses the layer (the M42 / M51 rule).
;;;
;;; Conventions: #nil is elisp nil; no module-level mutable state.
;;;
;;; FIX-20261008-guilemacs: M51 imp-4 known limits, recorded here so the
;;; whole-bytes family does not silently regress:
;;;   - Android assets.  image_open uses open-fdes only.  An Android
;;;     asset is not a plain path, so the open fails and the read
;;;     returns #f.  The old C path used android_open_asset through
;;;     image_find_image_fd.  The whole-bytes family therefore regresses
;;;     on HAVE_ANDROID.  The asset branch STAYS C (it is native platform
;;;     code); imp-5 records it with the other native paths.  This
;;;     module is not built for Android in imp-4.
;;;   - Remote file-name handlers.  image_resolve_path runs the elisp
;;;     handler through locate-file-internal, but the open here is a
;;;     local open-fdes, so a handler that resolves to a non-local name
;;;     fails and the read returns #f.

(define-module (emacs image)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:use-module (rnrs bytevectors)     ; bytevector?, bytevector-length
  #:use-module (ice-9 binary-ports)   ; open-fdes, fdopen, get-bytevector-n
  #:declarative? #t
  #:export (image-resolve-path
            image-open
            image-handle-read
            image-close
            image-read-file))

;; The elisp subrs the resolution policy uses.  `locate-file-internal'
;; runs the openp search (src/lread.c) in the same order as
;; image_find_image_fd and returns the found absolute name, or nil.
(defelisp %locate-file-internal locate-file-internal)
(defelisp %expand-file-name      expand-file-name)

;; The elisp list terminator: the Guile empty list or the elisp nil.
(define (image--end? lst)
  (or (null? lst) (eq? lst #nil)))

;; The search path: data-directory/images first, then x-bitmap-file-path.
;; This is the order image_find_image_fd uses.  `x-bitmap-file-path' may
;; be nil, so the list ends with #nil (the module convention).
(define (image--search-path)
  (let ((images ((force %expand-file-name)
                 "images" (symbol-value 'data-directory)))
        (xpath (symbol-value 'x-bitmap-file-path)))
    (cons images (if (image--end? xpath) #nil xpath))))

;; Resolve FILENAME to an absolute path string, or #f.  The ONE design
;; point of brief.org section 6: openp runs the elisp file-name handler.
;; Guile's file API does not know the handler, so the resolution runs
;; through the elisp subr `locate-file-internal', which honors the
;; handler.  The resolved name is then opened as a plain local port.  A
;; handler that resolves to a non-local name (a remote file) is not
;; supported by this imp-4 path; the local open fails and returns #f.
;;
;; The C bridge also calls this procedure to tell a "not found" miss
;; from a read error, and to get the resolved name for the SVG base URI
;; (FIX-20261008-guilemacs: M51 imp-4, review F3 / F4).
(define (image-resolve-path filename)
  (let ((found ((force %locate-file-internal)
                filename (image--search-path) #nil #nil)))
    (if (string? found) found #f)))

;; Open PATH for binary read as a Scheme-owned port, or #f on error.
;; Scheme opens the descriptor (open-fdes) and wraps it (fdopen).  The
;; port is owned by Scheme; C never closes a borrowed handle.
(define (image-open path)
  (catch #t
    (lambda () (fdopen (open-fdes path O_RDONLY) "rb"))
    (lambda args #f)))

;; The errno of a caught system error.  ARGS is the full argument list
;; the `system-error' handler received; system-error-errno reads the
;; errno slot.  Do not scan the list for any integer: an unrelated
;; integer (for example a file descriptor) can match by accident.
(define (image--system-errno args)
  (system-error-errno args))

;; An OS error we retry: EINTR or EAGAIN.  The handle contract
;; (docs/m51-plan.org) requires both to be retried inside the read, so
;; they never cross the boundary.
(define (image--retryable-errno? args)
  (let ((e (image--system-errno args)))
    (and (integer? e) (or (= e EINTR) (= e EAGAIN)))))

;; Read at most COUNT bytes from PORT.  Return a bytevector of at most
;; COUNT bytes, or #f at EOF.  A full read is normal.  A short read is
;; not an error.  Retry EINTR and EAGAIN here, so they never cross the
;; boundary (the handle contract of docs/m51-plan.org).
(define (image-handle-read port count)
  (let loop ()
    (let ((r (catch 'system-error
               (lambda () (get-bytevector-n port count))
               (lambda args
                 (if (image--retryable-errno? args)
                     'image--retry
                     (apply throw args))))))
      (cond ((eq? r 'image--retry) (loop))
            ((eof-object? r) #f)
            (else r)))))

;; Close PORT.  A #f port is a no-op.
(define (image-close port)
  (when port (close-port port)))

;; The whole-bytes entry.  Resolve FILENAME, open it, read to EOF, and
;; close the port in a dynamic-wind on the normal end and on a read
;; error.  Return a bytevector of all bytes, or #f on a miss or a read
;; error.  The growing-file check of the old C slurp_file runs here:
;; stat the port for the reported size, read at most reported-size + 1
;; bytes (the old fread buflen + 1 cap), and require the byte count to
;; equal the reported size.  A file that grew (count > size) or shrank
;; (count < size) during the read returns #f.  The +1 cap bounds the
;; read, so a file that grows without limit does not fill memory.  An
;; EMPTY file (size 0) returns an empty bytevector, as the old helper
;; returned a 0-size buffer; the decoder then reports its own error.
;; Any error returns #f, so no Scheme error crosses to C.
(define (image-read-file filename)
  (catch #t
    (lambda ()
      (let ((path (image-resolve-path filename)))
        (and path
             (let ((port (image-open path)))
               (and port
                    (dynamic-wind
                      (lambda () #t)
                      (lambda ()
                        (let ((size (stat:size (stat port))))
                          (let ((bv (get-bytevector-n port (1+ size))))
                            (cond ((eof-object? bv)
                                   (and (= size 0) (make-bytevector 0)))
                                  ((= (bytevector-length bv) size) bv)
                                  (else #f)))))
                      (lambda () (image-close port))))))))
    (lambda args #f)))
