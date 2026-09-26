;;; test-m42-imp2.scm --- M42 imp-2: Scheme TTY policy, C syscall leaves.
;;;
;;; The direct libc FFI version landed in f2ea65bf and was retired. The
;;; two C leaves --tty-bytes-readable and --tty-read-nonblocking are
;;; restored. (emacs gobble) keeps the input guard, read cap, decoding,
;;; quit handling, and event storage.
;;;
;;; This corpus tests the real Scheme policy with the C leaves stubbed,
;;; checks the leaves' neutral non-TTY behavior, and pins that the FFI
;;; path is absent. Real TTY syscall behavior belongs in the planned
;;; pseudo-terminal test.

(use-modules (srfi srfi-11))
(use-modules (srfi srfi-13))
(use-modules (rnrs bytevectors))
(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))
(use-modules (emacs gobble))
(use-modules (emacs event-modifiers))

(define test-results '())
(define (report name status)
  (set! test-results (cons (list name status) test-results)))
(define (check name expected actual)
  (report name (if (equal? expected actual) 'PASS
                   (list 'FAIL 'expected expected 'got actual))))
(define (bool name value) (report name (if value 'PASS 'FAIL)))

(define (slurp path)
  (if (not (file-exists? path)) #f
      (call-with-input-file path
        (lambda (port)
          (let loop ((chars '()))
            (let ((c (read-char port)))
              (if (eof-object? c) (list->string (reverse chars))
                  (loop (cons c chars)))))))))
(define (repo path) (string-append %m42-root "/" path))
(define (contains? text needle)
  (and (string? text) (string-contains text needle)))
(define (line-count text)
  (if (not (string? text)) 0
      (- (length (string-split text #\newline)) 1)))
(define (count-lines-starting text prefix)
  (if (not (string? text)) 0
      (let loop ((lines (string-split text #\newline)) (n 0))
        (if (null? lines) n
            (loop (cdr lines)
                  (if (string-prefix? prefix (car lines)) (+ n 1) n))))))
(define (before? text a b)
  (let ((ai (and (string? text) (string-contains text a)))
        (bi (and (string? text) (string-contains text b))))
    (and ai bi (< ai bi))))

(if (not (defined? '%m42-root))
    (begin (report "m42-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m42-root "."))
    (report "m42-root-bound" 'PASS))

(define gobble-mod (resolve-module '(emacs gobble)))
(define (with-delay! name proc thunk)
  (let ((old (module-ref gobble-mod name)))
    (dynamic-wind
      (lambda () (module-set! gobble-mod name (delay proc)))
      thunk
      (lambda () (module-set! gobble-mod name old)))))
(define (with-delays! entries thunk)
  (if (null? entries) (thunk)
      (with-delay! (caar entries) (cdar entries)
        (lambda () (with-delays! (cdr entries) thunk)))))

(define order '())
(define (record! x) (set! order (append order (list x))))
(define (run-read! overrides)
  (define (get key default)
    (let ((p (assq key overrides))) (if p (cdr p) default)))
  (let* ((bytes (get 'bytes '()))
         (avail (get 'avail (length bytes))))
    (set! order '())
    (let ((result
           (with-delays!
            (list
             (cons '%--kbd-buffer-nr-stored (lambda () (get 'stored 0)))
             (cons '%--kbd-on-hold-p (lambda () (get 'hold #nil)))
             (cons '%--tty-bytes-readable (lambda (term) avail))
             (cons '%--tty-read-nonblocking
                   (lambda (term n)
                     (record! (list 'read n))
                     (get 'read-result
                          (cons (length bytes) (u8-list->bytevector bytes)))))
             (cons '%--tty-meta-key (lambda (term) (get 'meta 0)))
             (cons '%--quit-char (lambda () (get 'quit 7)))
             (cons '%--tty-top-frame (lambda (term) 'frame))
             (cons '%--ie-ascii-keystroke-event
                   (lambda (code mods frame)
                     (record! (list 'event code mods)) 'event))
             (cons '%kbd-buffer-store-event!
                   (lambda (event hold) (record! 'store) #nil)))
            (lambda () (tty-read-avail-input! 'terminal)))))
      (values result order))))

(define (check-events name overrides expected ret)
  (let-values (((result events) (run-read! overrides)))
    (check (string-append "m42/imp2/" name "/return") ret result)
    (check (string-append "m42/imp2/" name "/events") expected events)))

(check-events "input" '((bytes . (65 66)))
              '((read 2) (event 65 0) store (event 66 0) store) 2)
(check-events "short-read" '((avail . 4) (bytes . (65 66)))
              '((read 4) (event 65 0) store (event 66 0) store) 2)
(check-events "meta" '((bytes . (193)) (meta . 1))
              (list '(read 1) (list 'event 65 meta-modifier) 'store) 1)
(check-events "quit" '((bytes . (65 135 66)))
              '((read 3) (event 65 0) store (event 7 0) store) 3)
(check-events "ioctl-error" '((avail . -2)) '() -2)
(check-events "eio" '((avail . 1) (read-result . -2)) '((read 1)) -2)
(check-events "read-error" '((avail . 1)
                              (read-result . (-1 . #vu8())))
              '((read 1)) -1)
(check-events "no-input" '((avail . 0)) '() 0)
(check-events "hold" '((hold . t) (bytes . (65))) '() 0)
(check-events "full-buffer" '((stored . 4095) (bytes . (65))) '() 0)

;; Source and surface pins protect the direction and measured baseline.
(define gob (slurp (repo "mod/emacs/gobble.scm")))
(define kb (slurp (repo "src/keyboard.c")))
(define kg (slurp (repo "src/keyboard-globals.c")))
(define rt (slurp (repo "tool/run-tests.scm")))
(bool "m42/imp2/no-system-foreign" (not (contains? gob "(system foreign)")))
(bool "m42/imp2/no-libc-link" (not (contains? gob "libc.so.6")))
(bool "m42/imp2/no-tty-fd" (not (contains? gob "%--tty-fd")))
(bool "m42/imp2/keeps-readable-leaf"
      (contains? gob "%--tty-bytes-readable"))
(bool "m42/imp2/keeps-read-leaf"
      (contains? gob "%--tty-read-nonblocking"))
(bool "m42/imp2/policy-in-scheme"
      (and (contains? gob "+cbuf-cap+")
           (contains? gob "%kbd-buffer-store-event!")))
(bool "m42/imp2/meta-order"
      (before? gob "(not (zero? (logand b #x80)))" "(logand b #x7f)"))
(check "m42/imp2/c/readable-defun" 1
       (count-lines-starting kb "DEFUN (\"--tty-bytes-readable\""))
(check "m42/imp2/c/read-defun" 1
       (count-lines-starting kb "DEFUN (\"--tty-read-nonblocking\""))
(check "m42/imp2/c/no-fd-defun" 0
       (count-lines-starting kb "DEFUN (\"--tty-fd\""))
(check "m42/imp2/c/defuns-446" 446 (count-lines-starting kb "DEFUN (\""))
(check "m42/imp2/c/combined-surface-11711" 11711
       (+ (line-count kb) (line-count kg)))
(bool "m42/imp2/harness-registered"
      (contains? rt "test/m42/test-m42-imp2.el"))
