(define-module (emacs modify-event-symbol)
  #:use-module (emacs elisp-ref)
  #:use-module (emacs-elisp runtime)
  #:use-module (emacs event-modifiers)
  #:declarative? #t
  #:export (modify-event-symbol
            cache-accent cache-func cache-mouse
            cache-wheel cache-drag-n-drop cache-pinch
            cache-system))

;;; imp-8.1.2 — modify_event_symbol port to Scheme.
;;;
;;; Replaces the C static modify_event_symbol (keyboard.c:8025–8110).
;;; The C body is deleted; its 7 callers now route through
;;; SCM_CALL_7 into this module's modify-event-symbol.
;;;
;;; Cache slots are read/written via --mes-cache-get / --mes-cache-set
;;; (imp-8.1.1), keyed by fixnum 0–6:
;;;   0 = accent_key_syms    1 = func_key_syms     2 = mouse_syms
;;;   3 = wheel_syms          4 = drag_n_drop_syms  5 = pinch_syms
;;;   6 = system_key_syms
;;;
;;; Traps already logged:
;;;   - apply-modifiers is imported directly from (emacs event-modifiers),
;;;     not routed through (%c 'apply-modifiers).
;;;   - symbol-int is a Guile fixnum; assq compares with eq? which works
;;;     on fixnums ≤ most-positive-fixnum.
;;;   - system_key_syms is lazy-inited inside --mes-cache-get (C side).

(defelisp %--mes-cache-get --mes-cache-get)
(defelisp %--mes-cache-set --mes-cache-set)

;;; Cache-ID constants — must match enum mes_cache_id in keyboard.c.
(define cache-accent      0)
(define cache-func        1)
(define cache-mouse       2)
(define cache-wheel       3)
(define cache-drag-n-drop 4)
(define cache-pinch       5)
(define cache-system      6)

(defelisp %--get-keysym-name --get-keysym-name)
(defelisp %intern intern)
(defelisp %put put)

(define (modify-event-symbol symbol-num modifiers kind
                             name-alist-or-stem name-vec
                             cache-id table-size)
  "Port of keyboard.c:modify_event_symbol (8025–8110).

SYMBOL-NUM:   key index (integer).
MODIFIERS:    modifier bitmask (integer).
KIND:         event-kind symbol, e.g. 'function-key or 'mouse-click.
NAME-ALIST-OR-STEM: alist, string stem, or #nil.
NAME-VEC:     pre-exposed lispy-key vector, or #nil when C used NULL.
CACHE-ID:     fixnum 0–6 selecting the C-side cache slot.
TABLE-SIZE:   expected cache-vector size (integer)."

  ;; Step 1: mask vendor-specific bit.
  (let ((symbol-int (logand symbol-num #xffffff)))

    ;; Step 2: range check.
    (if (or (< symbol-num 0) (>= symbol-num table-size))
        #nil

        ;; Step 3: read cache.
        (let* ((cache ((force %--mes-cache-get) cache-id))
               (value
                (if (pair? cache)
                    ;; Cons → alist lookup.
                    (let ((entry (assq symbol-int cache)))
                      (if (pair? entry) (cdr entry) #nil))
                    ;; Vector or nil → ensure vector, aref.
                    (begin
                      (unless (and (vector? cache)
                                   (= (vector-length cache) table-size))
                        (set! cache (make-vector table-size #nil)))
                      (vector-ref cache symbol-num)))))

          ;; Step 4: build value if nil.
          (when (eq? value #nil)
            (set! value
                  (cond
                   ((pair? name-alist-or-stem)
                    ;; Alist: assq symbol-int.
                    (let ((entry (assq symbol-int name-alist-or-stem)))
                      (if (pair? entry) (cdr entry) #nil)))
                   ((string? name-alist-or-stem)
                    ;; String stem: format "STEM-N".
                    ((force %intern)
                     (string-append name-alist-or-stem "-"
                                    (number->string (+ symbol-int 1)))))
                   ((and (vector? name-vec)
                         (< symbol-num (vector-length name-vec))
                         (vector-ref name-vec symbol-num))
                    => (lambda (v) ((force %intern) v)))
                   (else
                    ;; get-keysym-name fallback (imp-8.1.3).
                    (let ((name ((force %--get-keysym-name) symbol-num)))
                      (if name
                          ((force %intern) name)
                          ;; Final fallback: "key-N".
                          ((force %intern)
                           (string-append "key-"
                                          (number->string symbol-num))))))))

            ;; Step 5: write back to cache.
            (if (pair? cache)
                ((force %--mes-cache-set)
                 cache-id
                 (cons (cons symbol-int value) cache))
                (begin
                  (vector-set! cache symbol-num value)
                  ((force %--mes-cache-set) cache-id cache)))

            ;; Step 6: prime event-symbol-elements + event-kind.
            ;; (apply-modifiers with click_modifier fills the property caches;
            ;;  matching C's apply_modifiers (modifiers & click_modifier, value).)
            (apply-modifiers (logand modifiers click-modifier) value)
            ((force %put) value 'event-kind kind))

          ;; Step 7: apply modifiers and return.
          (apply-modifiers modifiers value)))))
