(define-module (emacs record)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export
   (elisp-record
    elisp-recordp
    init-record-registrations))

(define %elisp-record-type #f)
(define %elisp-record-constructor #f)
(define %elisp-record-predicate #f)
(define %elisp-record-accessor-type #f)
(define %elisp-record-accessor-len #f)
(define %elisp-record-accessor-slots #f)
(define %elisp-record-modifier-type #f)
(define %elisp-record-modifier-slots #f)

(define (elisp-record type . slots)
  (%elisp-record-constructor type
                             (1+ (length slots))
                             (list->vector (cons type slots))))

(define (elisp-make-record type len init)
  (let ((slotv (make-vector (1+ len) init)))
    (vector-set! slotv 0 type)
    (%elisp-record-constructor type
                               (1+ len)
                               slotv)))

(define (elisp-recordp rec)
  (if (%elisp-record-predicate rec)
      #t #nil))

(define (elisp-record-length rec)
  (%elisp-record-accessor-len rec))

(define (elisp-record-type rec)
  (%elisp-record-accessor-type rec))

(define (elisp-record-ref rec idx)
  (vector-ref (%elisp-record-accessor-slots rec)
              idx))

(define (elisp-record-slots rec)
  (%elisp-record-accessor-slots rec))

(define (elisp-record-set! rec idx val)
  (vector-set! (%elisp-record-accessor-slots rec)
               idx
               val))

(define (elisp-record-copy rec)
  (%elisp-record-constructor (%elisp-record-accessor-type rec)
                             (%elisp-record-accessor-len rec)
                             (vector-copy
                              (%elisp-record-accessor-slots rec))))

(define (init-record-registrations)
  ;
  (set! %elisp-record-type
        (make-record-type "elisp-record" '(type len slots)))
  (set! %elisp-record-constructor
        (record-constructor %elisp-record-type))
  (set! %elisp-record-predicate
        (record-predicate %elisp-record-type))
  (set! %elisp-record-accessor-type
        (record-accessor %elisp-record-type 'type))
  (set! %elisp-record-accessor-len
        (record-accessor %elisp-record-type 'len))
  (set! %elisp-record-accessor-slots
        (record-accessor %elisp-record-type 'slots))
  (set! %elisp-record-modifier-type
        (record-modifier %elisp-record-type 'type))
  (set! %elisp-record-modifier-slots
        (record-modifier %elisp-record-type 'slots))
  ;
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `((record ,elisp-record)
              (make-record ,elisp-make-record)
              (recordp ,elisp-recordp)
              (record-length ,elisp-record-length)
              (record-type ,elisp-record-type)
              (record-ref ,elisp-record-ref)
              (record-set ,elisp-record-set!)
              (record-copy ,elisp-record-copy)
              (record-slots ,elisp-record-slots)
              )))
