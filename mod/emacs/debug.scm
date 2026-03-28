(define-module (emacs debug)
  #:use-module (emacs-elisp runtime)
  #:use-module (system vm disassembler)
  #:use-module (system vm program)
  #:use-module (ice-9 format)
  #:use-module (ice-9 pretty-print)
  #:export
   (init-debug-registrations
    disassemble-elisp
    disassemble-elisp-to-string
    disassemble-elisp-sexp
    elisp-procedure-info))

;; Note: procedure-name and procedure-minimum-arity are in core Guile

;;; Debug utilities for inspecting elisp functions compiled to Guile bytecode.

(define (format-source src)
  "Format a source location record for display."
  (if src
      (format #f "~a:~a:~a"
              (or (source:file src) "<unknown>")
              (source:line-for-user src)
              (source:column src))
      "<no source>"))

(define (elisp-procedure-info sym)
  "Return detailed info about elisp function SYM as an alist.
Keys: name, arity, source, fbound, program?"
  (let ((proc (symbol-function sym)))
    (cond
     ((eq? proc #nil)
      `((fbound . #f)))
     ((not (procedure? proc))
      `((fbound . #t)
        (procedure? . #f)
        (value . ,proc)))
     ((not (program? proc))
      `((fbound . #t)
        (procedure? . #t)
        (program? . #f)
        (name . ,(procedure-name proc))
        (arity . ,(procedure-minimum-arity proc))))
     (else
      (let ((src (program-source proc 0)))
        `((fbound . #t)
          (procedure? . #t)
          (program? . #t)
          (name . ,(procedure-name proc))
          (arity . ,(procedure-minimum-arity proc))
          (source . ,(and src (format-source src)))
          (code-range . ,(program-address-range proc))
          (arguments . ,(program-arguments-alist proc))))))))

(define (disassemble-elisp-to-string sym)
  "Disassemble elisp function SYM and return the disassembly as a string.
SYM is the symbol name of an elisp defun (e.g., 'foo).
Returns a string containing:
  - Procedure metadata (name, arity, source location)
  - Guile VM bytecode disassembly"
  (let ((proc (symbol-function sym)))
    (cond
     ((eq? proc #nil)
      (format #f "Symbol '~a is not fbound~%" sym))
     ((not (procedure? proc))
      (format #f "Symbol '~a is not a procedure: ~s~%" sym proc))
     ((not (program? proc))
      (format #f "Symbol '~a is a procedure but not a compiled program: ~s~%~
                  (May be a primitive or closure)~%" sym proc))
     (else
      (call-with-output-string
        (lambda (port)
          (let ((src (program-source proc 0))
                (range (program-address-range proc))
                (args (program-arguments-alist proc)))
            (format port "=== Disassembly of elisp function '~a ===~%~%" sym)
            (format port "Procedure name: ~a~%" (or (procedure-name proc) "(anonymous)"))
            (format port "Minimum arity: ~a~%" (procedure-minimum-arity proc))
            (when args
              (format port "Arguments: ~s~%" args))
            (when src
              (format port "Source: ~a~%" (format-source src)))
            (when range
              (format port "Code range: #x~x - #x~x (~a bytes)~%"
                      (car range) (cdr range)
                      (- (cdr range) (car range))))
            (format port "~%--- Guile VM Bytecode ---~%~%")
            (disassemble-program proc port))))))))

(define (disassemble-elisp sym . args)
  "Disassemble elisp function SYM and print to current output port.
SYM is the symbol name of an elisp defun (e.g., 'foo).
Optional PORT argument specifies output port (default: current-output-port)."
  (let ((port (if (null? args) (current-output-port) (car args))))
    (display (disassemble-elisp-to-string sym) port)))

(define (collect-program-bytecode proc)
  "Collect bytecode instructions from PROC as a list of s-expressions.
Each instruction is a list like (opcode arg1 arg2 ...)."
  (reverse
   (fold-program-code
    (lambda (elt acc)
      (cons elt acc))
    '()
    proc)))

(define (disassemble-elisp-sexp sym)
  "Disassemble elisp function SYM and return as s-expression.
SYM is the symbol name of an elisp defun (e.g., 'foo).
Returns an alist with:
  - (name . symbol)
  - (arity . (nreq nopt rest?))
  - (arguments . alist)
  - (source . \"file:line:col\" or #f)
  - (code-range . (start . end))
  - (bytecode . ((opcode args ...) ...))

Returns ((error . message)) if function is not disassemblable."
  (let ((proc (symbol-function sym)))
    (cond
     ((eq? proc #nil)
      `((error . ,(format #f "Symbol '~a is not fbound" sym))))
     ((not (procedure? proc))
      `((error . ,(format #f "Symbol '~a is not a procedure" sym))
        (value . ,proc)))
     ((not (program? proc))
      `((error . ,(format #f "Symbol '~a is not a compiled program (may be primitive)" sym))
        (value . ,proc)))
     (else
      (let ((src (program-source proc 0)))
        `((name . ,sym)
          (procedure-name . ,(procedure-name proc))
          (arity . ,(procedure-minimum-arity proc))
          (arguments . ,(program-arguments-alist proc))
          (source . ,(and src (format-source src)))
          (code-range . ,(program-address-range proc))
          (bytecode . ,(collect-program-bytecode proc))))))))

(define (init-debug-registrations)
  "Initialize debug-related elisp functions."
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `((disassemble-elisp ,disassemble-elisp)
              (disassemble-elisp-to-string ,disassemble-elisp-to-string)
              (disassemble-elisp-sexp ,disassemble-elisp-sexp)
              (elisp-procedure-info ,elisp-procedure-info))))
