;;; test-m42-imp2.scm --- M42 imp-2: the TTY raw-input OS hop.
;;;
;;; brief.org (M42 imp-2) makes (emacs gobble) tty-read-avail-input!
;;; reach the OS with plain values.  The Scheme body calls the FFI read()
;;; and ioctl(FIONREAD) directly on a plain int fd (from the new C
;;; accessor --tty-fd) through (system foreign) and libc.so.6.  errno is
;;; read through __errno_location with the pointer captured once.  The
;;; two terminal-taking C shims --tty-bytes-readable and
;;; --tty-read-nonblocking are retired.
;;;
;;; Two kinds of check:
;;;   - real FFI probes on a pipe: pipe(2), write 3 bytes, then
;;;     ioctl(FIONREAD) returns 3 and read() returns 3 ("abc") -- the
;;;     imp-1 success probe, now a tracked test; plus a nonblocking
;;;     empty pipe where read() returns -1 and __errno_location reads
;;;     EAGAIN (11), which drives the errno-classification recipe.  Both
;;;     need no pty and no emacs C build beyond the embedded Guile.
;;;   - static scans of mod/emacs/gobble.scm, src/keyboard.c, and the
;;;     harness registration (the retirement pins, the FFI words, the
;;;     unchanged meta-decode order, the DEFUN count and surface).
;;;
;;; The repo root is bound by the .el wrapper as %m42-root.  The .el
;;; wrapper turns each (NAME PASS|FAIL) pair into an ERT test; see
;;; test/m42/test-m42-imp2.el.  The corpus reads no docs/ file.

(use-modules (srfi srfi-13))
(use-modules (system foreign))
(use-modules (rnrs bytevectors))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (bool name ok)
  (report name (if ok 'PASS 'FAIL)))

(define (slurp path)
  "Return the whole file at PATH as a string, or #f when it is absent."
  (if (not (file-exists? path))
      #f
      (call-with-input-file path
        (lambda (port)
          (let loop ((chars '()))
            (let ((c (read-char port)))
              (if (eof-object? c)
                  (list->string (reverse chars))
                  (loop (cons c chars)))))))))

(define (repo path) (string-append %m42-root "/" path))

(define (contains? text needle)
  (and (string? text)
       (if (string-contains text needle) #t #f)))

(define (count-occurrences text needle)
  "Count the non-overlapping occurrences of NEEDLE in TEXT."
  (if (not (string? text))
      0
      (let ((nlen (string-length needle)))
        (let loop ((start 0) (n 0))
          (let ((idx (string-contains text needle start)))
            (if (not idx)
                n
                (loop (+ idx nlen) (+ n 1))))))))

(define (count-lines-starting text prefix)
  "Count the lines of TEXT that start with PREFIX."
  (if (not (string? text))
      0
      (let loop ((lines (string-split text #\newline)) (n 0))
        (if (null? lines)
            n
            (loop (cdr lines)
                  (if (string-prefix? prefix (car lines)) (+ n 1) n))))))

(define (before? text a b)
  "True when A appears in TEXT and B appears after it."
  (and (string? text)
       (let ((ai (string-contains text a))
             (bi (string-contains text b)))
         (and ai bi (< ai bi)))))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m42-root))
    (begin (report "m42-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m42-root "."))
    (report "m42-root-bound" 'PASS))

;;; --- 1. The FFI probe on a pipe (real OS calls) --------------------
;;;
;;; The same recipe gobble.scm uses: (system foreign) over libc.so.6.
;;; pipe(2) gives a read fd with no tty; write 3 bytes to the write end;
;;; FIONREAD on the read fd reports 3; read() returns 3 ("abc").
(define %libc (dynamic-link "libc.so.6"))
(define (ffi name ret args)
  (pointer->procedure ret (dynamic-func name %libc) args))
(define %cpipe (ffi "pipe"  int (list '*)))
(define %cwrite (ffi "write" ssize_t (list int '* size_t)))
(define %cread (ffi "read"  int (list int '* size_t)))
(define %cioc  (ffi "ioctl" int (list int unsigned-long '*)))
(define %cclose (ffi "close" int (list int)))
(define +fionread+ #x541b)

(define (probe-pipe)
  "Run the FFI probe on a fresh pipe and return
(wrote ioctl-ok avail nread bytes) or (list 'pipe-failed)."
  (let ((fds (make-bytevector 8 0)))
    (if (not (zero? (%cpipe (bytevector->pointer fds))))
        (list 'pipe-failed)
        (let ((rfd (bytevector-s32-native-ref fds 0))
              (wfd (bytevector-s32-native-ref fds 4)))
          (let* ((msg (u8-list->bytevector (list 97 98 99)))
                 (wrote (%cwrite wfd (bytevector->pointer msg) 3))
                 (scratch (make-bytevector 4 0))
                 (ioctl-ok (zero? (%cioc rfd +fionread+
                                        (bytevector->pointer scratch))))
                 (avail (bytevector-sint-ref scratch 0 (native-endianness) 4))
                 (buf (make-bytevector 8 0))
                 (nread (%cread rfd (bytevector->pointer buf) 8))
                 (bytes (list (bytevector-u8-ref buf 0)
                              (bytevector-u8-ref buf 1)
                              (bytevector-u8-ref buf 2))))
            (%cclose rfd)
            (%cclose wfd)
            (list wrote ioctl-ok avail nread bytes))))))

(let ((r (catch #t
           (lambda () (probe-pipe))
           (lambda (key . args) (list 'error)))))
  (if (or (not (list? r)) (< (length r) 5) (eq? (car r) 'pipe-failed))
      (begin (bool "m42/imp2/probe/pipe" #f)
             (bool "m42/imp2/probe/fionread-ioctl-ok" #f)
             (bool "m42/imp2/probe/fionread-count-3" #f)
             (bool "m42/imp2/probe/read-count-3" #f)
             (bool "m42/imp2/probe/read-bytes-abc" #f))
      (begin
        (check "m42/imp2/probe/pipe-wrote-3" 3 (list-ref r 0))
        (bool  "m42/imp2/probe/fionread-ioctl-ok" (list-ref r 1))
        (check "m42/imp2/probe/fionread-count-3" 3 (list-ref r 2))
        (check "m42/imp2/probe/read-count-3" 3 (list-ref r 3))
        (check "m42/imp2/probe/read-bytes-abc" (list 97 98 99) (list-ref r 4)))))

;;; --- 1b. The FFI errno probe (a real failing read) -----------------
;;;
;;; The success probe above never reads errno.  gobble.scm reads errno
;;; through __errno_location to classify a failed read (EINTR / EIO /
;;; EAGAIN).  Drive that recipe on a real failure: make the read end of
;;; an empty pipe nonblocking with fcntl(F_SETFL, O_NONBLOCK); read()
;;; then returns -1 and __errno_location must read EAGAIN (11).  This
;;; needs no pty and no emacs C build.
(define %cfcntl (ffi "fcntl" int (list int int int)))
(define %cerrno-location (ffi "__errno_location" '* '()))
(define %cerrno-cell (pointer->bytevector (%cerrno-location) 4))
(define (peek-errno)
  (bytevector-sint-ref %cerrno-cell 0 (native-endianness) 4))
(define +f-getfl+    3)
(define +f-setfl+    4)
(define +o-nonblock+ 2048)   ; 0x800 on Linux
(define +eagain+     11)

(define (probe-eagain)
  "On an empty nonblocking pipe, read() returns -1 and errno is EAGAIN.
Return (set-ok nread errno) or (list 'pipe-failed)."
  (let ((fds (make-bytevector 8 0)))
    (if (not (zero? (%cpipe (bytevector->pointer fds))))
        (list 'pipe-failed)
        (let ((rfd (bytevector-s32-native-ref fds 0))
              (wfd (bytevector-s32-native-ref fds 4)))
          (let* ((flags (%cfcntl rfd +f-getfl+ 0))
                 (set-ok (%cfcntl rfd +f-setfl+ (logior flags +o-nonblock+)))
                 (buf (make-bytevector 4 0))
                 (nread (%cread rfd (bytevector->pointer buf) 4))
                 (e (peek-errno)))
            (%cclose rfd)
            (%cclose wfd)
            (list set-ok nread e))))))

(let ((r (catch #t
           (lambda () (probe-eagain))
           (lambda (key . args) (list 'error)))))
  (if (or (not (list? r)) (< (length r) 3) (eq? (car r) 'pipe-failed))
      (begin (bool "m42/imp2/probe-eagain/set-nonblock-ok" #f)
             (bool "m42/imp2/probe-eagain/read-returns--1" #f)
             (bool "m42/imp2/probe-eagain/errno-eagain-11" #f))
      (begin
        (bool  "m42/imp2/probe-eagain/set-nonblock-ok" (zero? (list-ref r 0)))
        (check "m42/imp2/probe-eagain/read-returns--1" -1 (list-ref r 1))
        (check "m42/imp2/probe-eagain/errno-eagain-11" 11 (list-ref r 2)))))

;;; --- 2. Static: the module source (mod/emacs/gobble.scm) -----------
(define gob (slurp (repo "mod/emacs/gobble.scm")))
(bool "m42/imp2/module/exists" (and (string? gob) #t))

;; The FFI bindings and the errno read are present.
(bool "m42/imp2/module/imports-system-foreign" (contains? gob "(system foreign)"))
(bool "m42/imp2/module/links-libc-so-6" (contains? gob "libc.so.6"))
(bool "m42/imp2/module/errno-location" (contains? gob "__errno_location"))
(bool "m42/imp2/module/fionread-word" (contains? gob "FIONREAD"))
(bool "m42/imp2/module/fionread-const" (contains? gob "#x541b"))
(bool "m42/imp2/module/eintr-retry-word" (contains? gob "EINTR"))
(bool "m42/imp2/module/eagain-word" (contains? gob "EAGAIN"))
(bool "m42/imp2/module/eio-word" (contains? gob "EIO"))
(bool "m42/imp2/module/ioctl-fn" (contains? gob "(%ioctl fd +fionread+"))
(bool "m42/imp2/module/read-into-bytevector" (contains? gob "(%read fd (bytevector->pointer bv) count)"))

;; The two old shims are retired; --tty-fd exists.
(bool "m42/imp2/module/no-bytes-readable" (not (contains? gob "%--tty-bytes-readable")))
(bool "m42/imp2/module/no-read-nonblocking" (not (contains? gob "%--tty-read-nonblocking")))
(bool "m42/imp2/module/has-tty-fd" (contains? gob "%--tty-fd"))
(bool "m42/imp2/module/defelisp-tty-fd" (contains? gob "(defelisp %--tty-fd"))

;; The read policy stays in Scheme: the guard, the cap, and the store.
(bool "m42/imp2/module/keeps-on-hold-guard" (contains? gob "%--kbd-on-hold-p"))
(bool "m42/imp2/module/keeps-cbuf-cap" (contains? gob "+cbuf-cap+"))
(bool "m42/imp2/module/keeps-store" (contains? gob "%kbd-buffer-store-event!"))

;; The meta-decode order is unchanged: the modifier is computed from the
;; original byte (meta_key == 1), the byte is stripped to 7 bits
;; (meta_key < 2), and the STRIPPED code is compared against the quit
;; char.  A reversed order would zero the meta modifier.
(bool "m42/imp2/module/meta-order-mods-before-strip"
      (before? gob "(not (zero? (logand b #x80)))" "(logand b #x7f)"))
(bool "m42/imp2/module/meta-order-strip-before-quit"
      (before? gob "(logand b #x7f)" "(= code quit)"))
(bool "m42/imp2/module/meta-order-mods-before-quit"
      (before? gob "(not (zero? (logand b #x80)))" "(= code quit)"))

;;; --- 3. Static: the C side (src/keyboard.c) ------------------------
(define kb (slurp (repo "src/keyboard.c")))
(define kg (slurp (repo "src/keyboard-globals.c")))
(bool "m42/imp2/c/keyboard-exists" (and (string? kb) #t))

;; The new accessor exists; the two old shims are gone.
(check "m42/imp2/c/defun-tty-fd" 1
       (count-lines-starting kb "DEFUN (\"--tty-fd\""))
(check "m42/imp2/c/no-defun-bytes-readable" 0
       (count-lines-starting kb "DEFUN (\"--tty-bytes-readable\""))
(check "m42/imp2/c/no-defun-read-nonblocking" 0
       (count-lines-starting kb "DEFUN (\"--tty-read-nonblocking\""))

;; The re-measured surface.  Base 446 DEFUNs; imp-2 retires the two
;; shims (-2) and adds --tty-fd (+1), so the file holds 445.
;; (brief.org §3 states "444 (446 - 2)", which counts the two retires
;; but not the new accessor; 445 is the value the deliverables produce.)
(check "m42/imp2/c/defuns-445" 445
       (count-lines-starting kb "DEFUN (\""))
;; A `wc -l' line count: string-split on a text that ends in a newline
;; yields a final "" element, so the count is (length - 1).
(define (line-count text)
  (if (not (string? text)) 0 (- (length (string-split text #\newline)) 1)))
(bool "m42/imp2/c/keyboard-globals-exists" (and (string? kg) #t))
(check "m42/imp2/c/combined-surface-11666-exact"
       11666
       (+ (line-count kb) (line-count kg)))
(bool "m42/imp2/c/combined-surface-le-11960"
      (<= (+ (line-count kb) (line-count kg)) 11960))

;;; --- 4. Static: the harness registers this corpus ------------------
(define rt (slurp (repo "tool/run-tests.scm")))
(bool "m42/imp2/run-tests/group-m42" (contains? rt "(group (m42)"))
(bool "m42/imp2/run-tests/registers-el"
      (contains? rt "test/m42/test-m42-imp2.el"))
