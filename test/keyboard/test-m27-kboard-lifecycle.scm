;;; test-m27-kboard-lifecycle.scm --- M27 imp-2 (emacs kboard-lifecycle)
;;;   test corpus.
;;;
;;; Covers the M27 imp-2 cutover (brief.org M27 imp-2): the init_kboard
;;; field-default policy moved out of src/keyboard.c into (emacs
;;; kboard-lifecycle) as init-kboard!.  The C dispatcher keeps only the
;;; raw C-only field defaults (immediate_echo, kbd_macro_buffer,
;;; kbd_macro_bufsize, reference_count); every Lisp_Object field default,
;;; the kbd_queue_has_data clear, and the two-keymap wiring dispatch
;;; here.  This corpus exercises init-kboard! over stubbed setters:
;;;
;;;   - every nil-defaulting Lisp_Object field setter receives (KB #nil);
;;;   - window-system receives (KB TYPE);
;;;   - kbd_queue_has_data is cleared (val #nil);
;;;   - two fresh sparse keymaps are made and input-decode-map /
;;;     local-function-key-map each receive one (in that order);
;;;   - local-function-key-map's parent is wired to Vfunction_key_map;
;;;   - init-kboard! is an exported procedure (the C dispatcher's
;;;     scm_c_public_ref target).
;;;
;;; kboard-lifecycle.scm references its C primitives through defelisp
;;; delays ((force %...)), so these tests stub those delays by replacing
;;; them inside the (emacs kboard-lifecycle) module (module-set!),
;;; restoring after — the same stub mechanism test-m27-single-kboard.scm
;;; (imp-1) and test-m25-*.scm use.  Every stub is restored in a
;;; dynamic-wind unwind, so nothing leaks into later corpora
;;; ([[shared-harness-cross-corpus-state-leak]]).
;;;
;;; Sourced by test/keyboard/test-m27-kboard-lifecycle.el via
;;; eval-scheme.  Accumulates PASS/FAIL entries into `test-results` for
;;; readback from elisp.  See brief.org M27 imp-2.
;;;
;;; Live multi-terminal field-default verification (the imp-2 exit
;;; criterion) cannot run in this sandbox: creating a second terminal
;;; requires a real multi-tty session.  Recorded here explicitly instead
;;; of skipped silently; the single live boot exercises the dispatcher
;;; for the initial kboard.

(use-modules (emacs kboard-lifecycle))
(use-modules (emacs elisp-ref))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

;;; --- Stub helpers ----------------------------------------------------

(define kl-mod (resolve-module '(emacs kboard-lifecycle)))

;; The 15 nil-only Lisp_Object field setters init-kboard! must call with
;; (KB #nil).  window-system, input-decode-map and local-function-key-map
;; are covered separately (they receive TYPE / fresh keymaps).
(define nil-field-vars
  '(%set-kboard-overriding-terminal-local-map
    %set-kboard-last-command
    %set-kboard-real-last-command
    %set-kboard-keyboard-translate-table
    %set-kboard-last-repeatable-command
    %set-kboard-prefix-arg
    %set-kboard-last-prefix-arg
    %set-kboard-kbd-queue
    %set-kboard-defining-kbd-macro
    %set-kboard-last-kbd-macro
    %set-kboard-system-key-alist
    %set-kboard-system-key-syms
    %set-kboard-echo-string
    %set-kboard-echo-prompt
    %set-kboard-default-minibuffer-frame))

;; The full set of delay variables stubbed (must all be restored).
(define stub-var-names
  (append nil-field-vars
          '(%set-kboard-window-system
            %--set-kboard-kbd-queue-has-data
            %set-kboard-input-decode-map
            %set-kboard-local-function-key-map
            %make-sparse-keymap
            %set-keymap-parent)))

;; Run THUNK (receiving LOG, a list of (SETTER-NAME . ARGS) entries in
;; call order) with every (emacs kboard-lifecycle) C delay replaced by a
;; recording stub.  make-sparse-keymap returns fresh distinct map tokens
;; ('map-1, 'map-2, ...).  Restores all delays afterwards.
(define (run-with-kb-fakes! kb type thunk)
  (let ((log '())
        (map-n 0))
    (define (note name . args) (set! log (cons (cons name args) log)))
    (define (nil-stub name)
      (lambda args (apply note name args) #nil))
    (define (make-map-fn)
      ;; init-kboard! calls (make-sparse-keymap #nil); return a function
      ;; that accepts that optional arg and mints a fresh map token.
      (lambda (_arg)
        (set! map-n (1+ map-n))
        (note 'make-sparse-keymap)
        (string->symbol (string-append "map-" (number->string map-n)))))
    (let ((originals (map (lambda (nm) (module-ref kl-mod nm))
                          stub-var-names)))
      (dynamic-wind
        (lambda ()
          (for-each
           (lambda (nm)
             (module-set! kl-mod nm (delay (nil-stub nm))))
           nil-field-vars)
          (module-set! kl-mod '%set-kboard-window-system
                       (delay (lambda (k v) (note 'window-system k v) #nil)))
          (module-set! kl-mod '%--set-kboard-kbd-queue-has-data
                       (delay (lambda (k v) (note 'kbd-queue-has-data k v) v)))
          (module-set! kl-mod '%set-kboard-input-decode-map
                       (delay (lambda (k m) (note 'input-decode-map k m) #nil)))
          (module-set! kl-mod '%set-kboard-local-function-key-map
                       (delay (lambda (k m) (note 'local-function-key-map k m) #nil)))
          (module-set! kl-mod '%make-sparse-keymap
                       (delay (make-map-fn)))
          (module-set! kl-mod '%set-keymap-parent
                       (delay (lambda (m p) (note 'set-keymap-parent m p) #nil))))
        (lambda ()
          (init-kboard! kb type)
          (thunk log))
        (lambda ()
          (let loop ((names stub-var-names) (saved originals))
            (unless (null? names)
              (module-set! kl-mod (car names) (car saved))
              (loop (cdr names) (cdr saved)))))))))

;; Search LOG for a (NAME . ARGS) entry; return ARGS or #f if absent.
(define (find-args log name)
  (let ((hit (assq name log)))
    (and hit (cdr hit))))

(define (count-of log name)
  (length (filter (lambda (e) (eq? (car e) name)) log)))

;;; --- 1. nil-defaulting field setters ---------------------------------

(run-with-kb-fakes! 'kb-obj 'my-type
  (lambda (log)
    (for-each
     (lambda (nm)
       (let ((args (find-args log nm)))
         (check (string-append "init-kboard!/nil-set-" (symbol->string nm))
                (list 'kb-obj #nil)
                args)))
     nil-field-vars)))

;;; --- 2. window-system / kbd_queue_has_data ---------------------------

(run-with-kb-fakes! 'kb-obj 'my-type
  (lambda (log)
    (check "init-kboard!/window-system-receives-type"
           (list 'kb-obj 'my-type)
           (find-args log 'window-system))
    (check "init-kboard!/kbd-queue-has-data-cleared"
           (list 'kb-obj #nil)
           (find-args log 'kbd-queue-has-data))))

;;; --- 3. keymap wiring ------------------------------------------------

(run-with-kb-fakes! 'kb-obj 'my-type
  (lambda (log)
    ;; Two fresh keymaps were made, in order.
    (check "init-kboard!/make-sparse-keymap-twice" 2
           (count-of log 'make-sparse-keymap))
    (check "init-kboard!/input-decode-map-gets-first-map"
           (list 'kb-obj 'map-1)
           (find-args log 'input-decode-map))
    (check "init-kboard!/local-function-key-map-gets-second-map"
           (list 'kb-obj 'map-2)
           (find-args log 'local-function-key-map))
    ;; The two made maps differ (each field gets its own fresh map).
    (check "init-kboard!/two-distinct-maps"
           (not (eq? (cadr (find-args log 'input-decode-map))
                     (cadr (find-args log 'local-function-key-map))))
           #t)
    ;; local-function-key-map's map is wired to Vfunction_key_map.
    (check "init-kboard!/parent-wired-to-function-key-map"
           (list 'map-2 ((%c 'symbol-value) 'function-key-map))
           (find-args log 'set-keymap-parent))))

;;; --- 4. Coverage / single-call ---------------------------------------

(run-with-kb-fakes! 'kb-obj 'my-type
  (lambda (log)
    ;; Every nil-only field setter fired exactly once.
    (for-each
     (lambda (nm)
       (check (string-append "init-kboard!/single-nil-set-" (symbol->string nm))
              1
              (count-of log nm)))
     nil-field-vars)
    ;; window-system, the queue clear and both keymap setters fire once.
    (check "init-kboard!/window-system-once" 1
           (count-of log 'window-system))
    (check "init-kboard!/kbd-queue-has-data-once" 1
           (count-of log 'kbd-queue-has-data))
    (check "init-kboard!/input-decode-map-once" 1
           (count-of log 'input-decode-map))
    (check "init-kboard!/local-function-key-map-once" 1
           (count-of log 'local-function-key-map))
    (check "init-kboard!/set-keymap-parent-once" 1
           (count-of log 'set-keymap-parent))))

;;; --- 5. Export -------------------------------------------------------

;; The C dispatcher resolves init-kboard! via scm_c_public_ref; verify it
;; is an exported procedure of the module.
(check "kboard-lifecycle/exported-init-kboard!" #t
       (procedure? (module-ref (resolve-interface '(emacs kboard-lifecycle))
                               'init-kboard!)))
