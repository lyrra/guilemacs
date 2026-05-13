(define-module (emacs event-modifiers)
  #:use-module (emacs-elisp runtime)
  #:use-module (srfi srfi-11)   ; let-values
  #:declarative? #t
  #:export (parse-modifiers
            apply-modifiers
            reorder-modifiers
            event-convert-list
            event-symbol-parse-modifiers
            modifier-bit
            ;; Internal — exported so C shims in keyboard.c can reach them.
            parse-modifiers-uncached
            apply-modifiers-uncached
            lispy-modifier-list
            parse-solitary-modifier
            make-ctrl-char
            ;; Wiring.
            init-event-modifiers-registrations))

;;; M1 — Modifier parsing for the keyboard.c → Guile port.
;;;
;;; Replaces these C functions in src/keyboard.c (lines ~7185–7818):
;;;   parse_modifiers_uncached, parse_modifiers,
;;;   apply_modifiers_uncached, apply_modifiers,
;;;   reorder_modifiers, lispy_modifier_list,
;;;   parse_solitary_modifier,
;;;   Fevent_symbol_parse_modifiers, Fevent_convert_list,
;;;   make_ctrl_char.
;;;
;;; Caching uses elisp plist properties on symbols (event-symbol-element-mask,
;;; event-symbol-elements, modifier-cache, event-kind), matching the C
;;; semantics so any elisp that inspects the properties keeps working.
;;;
;;; TODO (follow-up after M1 closes): consider switching the parse_modifiers /
;;; apply_modifiers caches from symbol-plist to a per-module srfi-69
;;; eq?-hash-table.  Plist lookup walks a flat list; a hash table is O(1) and
;;; would avoid mutating user-observable symbol properties.  Hold until we
;;; have a per-keystroke benchmark (M5) — only flip if plist lookup shows
;;; up.

;;;;
;;;; Modifier bit constants  (from src/lisp.h:2895–2903 and src/termhooks.h:319)
;;;;

(define char-alt   #x0400000)
(define char-super #x0800000)
(define char-hyper #x1000000)
(define char-shift #x2000000)
(define char-ctl   #x4000000)
(define char-meta  #x8000000)

(define char-modifier-mask
  (logior char-alt char-super char-hyper char-shift char-ctl char-meta))

;; Aliases matching termhooks.h naming.
(define alt-modifier    char-alt)
(define super-modifier  char-super)
(define hyper-modifier  char-hyper)
(define shift-modifier  char-shift)
(define ctrl-modifier   char-ctl)
(define meta-modifier   char-meta)

;; Mouse-event modifier bits (low bits, distinct namespace).
(define up-modifier      1)
(define down-modifier    2)
(define drag-modifier    4)
(define click-modifier   8)
(define double-modifier 16)
(define triple-modifier 32)

(define characterbits 22)
(define key-to-char-mask (- (ash 1 characterbits) 1))

(define (key-to-char k) (logand k key-to-char-mask))

;;;;
;;;; Modifier-name table  (mirrors keyboard.c:7344, indexed by bit position)
;;;;

(define modifier-names-vec
  ;;  0    1     2     3      4       5     6 7 ... 21  22  23    24    25    26      27
  #(up down  drag  click  double triple #f #f #f #f #f #f #f #f #f #f #f #f #f #f #f #f
    alt super hyper shift control meta))

(define num-mod-bits (vector-length modifier-names-vec))

;;;;
;;;; Elisp-aware symbol predicate
;;;;
;;;; In Guile's elisp dialect, the elisp symbols `t' and `nil' are
;;;; represented as Scheme #t and #nil for performance.  Both are
;;;; symbols from elisp's point of view (C's SYMBOLP returns true for
;;;; them) but Scheme's symbol? rejects #t/#nil.  We need a predicate
;;;; that matches C SYMBOLP semantics, plus a name accessor that
;;;; handles the schemified forms.

(define (elisp-symbol? x)
  (or (symbol? x) (eq? x #t) (eq? x #nil)))

(define (elisp-symbol->string sym)
  (cond ((symbol? sym) (symbol->string sym))
        ((eq? sym #t)   "t")
        ((eq? sym #nil) "nil")
        (else (error "elisp-symbol->string: not a symbol" sym))))

;;;;
;;;; Plist helpers  (operate on symbol's plist directly)
;;;;

(define (plist-get sym key)
  (let loop ((pl (symbol-plist sym)))
    (cond
     ((or (null? pl) (not (pair? pl)) (not (pair? (cdr pl)))) #nil)
     ((eq? (car pl) key) (cadr pl))
     (else (loop (cddr pl))))))

(define (plist-put! sym key val)
  (let loop ((pl (symbol-plist sym)) (acc '()) (found? #f))
    (cond
     ((or (null? pl) (not (pair? pl)) (not (pair? (cdr pl))))
      (set-symbol-plist! sym
                         (if found?
                             (reverse acc)
                             (cons key (cons val (reverse acc))))))
     ((eq? (car pl) key)
      (loop (cddr pl) (cons val (cons key acc)) #t))
     (else
      (loop (cddr pl) (cons (cadr pl) (cons (car pl) acc)) found?)))))

;;;;
;;;; modifier-bit  (constant lookup, no parsing)
;;;;

(define (modifier-bit name)
  "Return the integer bit value for modifier NAME, or 0 if unknown."
  (case name
    ((alt)            alt-modifier)
    ((ctrl control)   ctrl-modifier)
    ((hyper)          hyper-modifier)
    ((meta)           meta-modifier)
    ((shift)          shift-modifier)
    ((super)          super-modifier)
    ((up)             up-modifier)
    ((down)           down-modifier)
    ((drag)           drag-modifier)
    ((click)          click-modifier)
    ((double)         double-modifier)
    ((triple)         triple-modifier)
    (else             0)))

;;;;
;;;; parse-modifiers-uncached
;;;;

(define (substring=? name start s)
  (let ((slen (string-length s))
        (nlen (string-length name)))
    (and (<= (+ start slen) nlen)
         (string=? (substring name start (+ start slen)) s))))

(define (modifier-prefix-at name i)
  "Return (values BITS END) for the modifier prefix at position I in NAME.
   END is the index just past the modifier (before the expected dash).
   Returns (values 0 0) if no modifier prefix is recognized.

   Mirrors parse_modifiers_uncached's per-character switch."
  (let ((len (string-length name)))
    (if (>= i len) (values 0 0)
        (case (string-ref name i)
          ((#\A) (values alt-modifier   (+ i 1)))
          ((#\C) (values ctrl-modifier  (+ i 1)))
          ((#\H) (values hyper-modifier (+ i 1)))
          ((#\M) (values meta-modifier  (+ i 1)))
          ((#\S) (values shift-modifier (+ i 1)))
          ((#\s) (values super-modifier (+ i 1)))
          ((#\d)
           (cond
            ((substring=? name i "drag")   (values drag-modifier   (+ i 4)))
            ((substring=? name i "down")   (values down-modifier   (+ i 4)))
            ((substring=? name i "double") (values double-modifier (+ i 6)))
            (else (values 0 0))))
          ((#\t)
           (if (substring=? name i "triple") (values triple-modifier (+ i 6))
               (values 0 0)))
          ((#\u)
           (if (substring=? name i "up") (values up-modifier (+ i 2))
               (values 0 0)))
          (else (values 0 0))))))

(define (parse-modifiers-uncached sym)
  "Parse SYM's name for modifier prefixes.  Return (values BITS END), where
   END is the byte offset where the unmodified base name starts."
  (let* ((name (elisp-symbol->string sym))
         (len (string-length name)))
    (let-values
        (((modifiers end)
          (let loop ((i 0) (modifiers 0))
            (if (>= i (- len 1))
                (values modifiers i)
                (call-with-values (lambda () (modifier-prefix-at name i))
                  (lambda (this-mod this-mod-end)
                    (cond
                     ((zero? this-mod-end) (values modifiers i))
                     ((or (>= this-mod-end len)
                          (not (char=? #\- (string-ref name this-mod-end))))
                      (values modifiers i))
                     (else
                      (loop (+ this-mod-end 1) (logior modifiers this-mod))))))))))
      ;; Implicit click-modifier for mouse-N and wheel- bases.
      (let* ((click-from-mouse?
              (and (zero? (logand modifiers
                                  (logior down-modifier drag-modifier
                                          double-modifier triple-modifier)))
                   (= (+ end 7) len)
                   (substring=? name end "mouse-")
                   (let ((c (string-ref name (+ end 6))))
                     (and (char>=? c #\0) (char<=? c #\9)))))
             (click-from-wheel?
              (and (zero? (logand modifiers
                                  (logior double-modifier triple-modifier)))
                   (< (+ end 6) len)
                   (substring=? name end "wheel-")))
             (modifiers
              (if (or click-from-mouse? click-from-wheel?)
                  (logior modifiers click-modifier)
                  modifiers)))
        (values modifiers end)))))

;;;;
;;;; apply-modifiers-uncached
;;;;

(define (apply-modifiers-uncached modifiers base-string)
  "Build the prefix string for MODIFIERS and prepend to BASE-STRING; intern."
  (let* ((prefix
          (string-append
           (if (zero? (logand modifiers alt-modifier))    "" "A-")
           (if (zero? (logand modifiers ctrl-modifier))   "" "C-")
           (if (zero? (logand modifiers hyper-modifier))  "" "H-")
           (if (zero? (logand modifiers meta-modifier))   "" "M-")
           (if (zero? (logand modifiers shift-modifier))  "" "S-")
           (if (zero? (logand modifiers super-modifier))  "" "s-")
           (if (zero? (logand modifiers double-modifier)) "" "double-")
           (if (zero? (logand modifiers triple-modifier)) "" "triple-")
           (if (zero? (logand modifiers up-modifier))     "" "up-")
           (if (zero? (logand modifiers down-modifier))   "" "down-")
           (if (zero? (logand modifiers drag-modifier))   "" "drag-")
           ;; click-modifier is implicit — absence of others denotes click.
           )))
    (string->symbol (string-append prefix base-string))))

;;;;
;;;; lispy-modifier-list
;;;;

(define (lispy-modifier-list modifiers)
  "Return the list of modifier symbols set in MODIFIERS.  Highest-bit-first.
   Terminates with #nil so the elisp `equal' agrees with the C list2 form."
  (let loop ((i 0) (acc #nil))
    (cond
     ((or (> (ash 1 i) modifiers) (>= i num-mod-bits)) acc)
     (else
      (let ((bit (ash 1 i))
            (name (vector-ref modifier-names-vec i)))
        (if (and name (not (zero? (logand modifiers bit))))
            (loop (+ i 1) (cons name acc))
            (loop (+ i 1) acc)))))))

;;;;
;;;; parse-modifiers
;;;;

(define event-symbol-element-mask 'event-symbol-element-mask)
(define event-symbol-elements     'event-symbol-elements)
(define modifier-cache            'modifier-cache)
(define event-kind                'event-kind)

(define (parse-modifiers sym)
  "Parse SYM (symbol or integer) into (BASE BITS), caching on the plist.

   For integers: returns (CHAR-CODE MODIFIER-BITS) where CHAR-CODE is the
   low CHARACTERBITS bits.  For symbols: caches under
   'event-symbol-element-mask and also populates 'event-symbol-elements
   with (BASE . LISPY-MODIFIER-LIST).  Returns #nil for unsupported
   types (matching C parse_modifiers's NIL fallthrough)."
  (cond
   ((integer? sym)
    ;; Cons-of-cons-of-nil form matches C's list2i so elisp `equal' agrees.
    (cons (key-to-char sym)
          (cons (logand sym char-modifier-mask) #nil)))
   ((not (elisp-symbol? sym))
    #nil)
   (else
    (let ((cached (plist-get sym event-symbol-element-mask)))
      (if (pair? cached)
          cached
          (call-with-values (lambda () (parse-modifiers-uncached sym))
            (lambda (modifiers end)
              (let* ((name (elisp-symbol->string sym))
                     (unmodified (string->symbol (substring name end)))
                     ;; cons-of-cons-of-nil — matches C list2 termination.
                     (elements (cons unmodified (cons modifiers #nil))))
                (plist-put! sym event-symbol-element-mask elements)
                (plist-put! sym event-symbol-elements
                            (cons unmodified (lispy-modifier-list modifiers)))
                elements))))))))

;;;;
;;;; apply-modifiers
;;;;

(define (apply-modifiers modifiers base)
  "Apply MODIFIERS (bit mask) to BASE (symbol or integer).  For symbols,
   caches under BASE's 'modifier-cache plist property and copies BASE's
   'event-kind to the new symbol.  Non-symbol non-integer input is
   returned unchanged (mirrors C's tolerant fallthrough)."
  (cond
   ((integer? base)
    (logior base modifiers))
   ((not (elisp-symbol? base))
    base)
   (else
    (let* ((cache (plist-get base modifier-cache))
           (cache (if (pair? cache) cache '()))
           (idx   (logand modifiers (lognot click-modifier)))
           (entry (assv idx cache)))
      (cond
       ((pair? entry) (cdr entry))
       (else
        (let* ((new-sym (apply-modifiers-uncached modifiers (elisp-symbol->string base)))
               (new-entry (cons idx new-sym)))
          (plist-put! base modifier-cache (cons new-entry cache))
          ;; Copy 'event-kind from base if new-sym doesn't have one yet.
          (let ((new-kind (plist-get new-sym event-kind)))
            (when (or (null? new-kind) (eq? new-kind #nil))
              (let ((base-kind (plist-get base event-kind)))
                (unless (or (null? base-kind) (eq? base-kind #nil))
                  (plist-put! new-sym event-kind base-kind)))))
          new-sym)))))))

;;;;
;;;; reorder-modifiers
;;;;

(define (reorder-modifiers sym)
  "Return SYM with its modifier prefixes in canonical order."
  (let ((parsed (parse-modifiers sym)))
    (cond
     ((pair? parsed)
      (apply-modifiers (cadr parsed) (car parsed)))
     (else
      ;; parse-modifiers returned #nil for non-symbol/non-integer input.
      ;; C's reorder_modifiers would XCAR/XCDR through nil and devolve
      ;; to apply_modifiers(0, Qnil) → the 'nil symbol.  Return SYM
      ;; unchanged here: callers receive the same surface value back,
      ;; no exception is raised, and no spurious symbols are interned.
      sym))))

;;;;
;;;; parse-solitary-modifier  (for list elements in event-convert-list)
;;;;

(define (parse-solitary-modifier sym)
  "Return the bit value if SYM names a modifier, else 0.  Matches the
   set recognized by event-convert-list elements."
  (cond
   ((not (elisp-symbol? sym)) 0)
   (else
    (let* ((name (elisp-symbol->string sym))
           (len (string-length name)))
      (cond
       ((zero? len) 0)
       (else
        (case (string-ref name 0)
          ((#\A) (if (= len 1) alt-modifier 0))
          ((#\a) (if (string=? name "alt") alt-modifier 0))
          ((#\C) (if (= len 1) ctrl-modifier 0))
          ((#\c) (cond
                  ((string=? name "ctrl")    ctrl-modifier)
                  ((string=? name "control") ctrl-modifier)
                  ((string=? name "click")   click-modifier)
                  (else 0)))
          ((#\H) (if (= len 1) hyper-modifier 0))
          ((#\h) (if (string=? name "hyper") hyper-modifier 0))
          ((#\M) (if (= len 1) meta-modifier 0))
          ((#\m) (if (string=? name "meta") meta-modifier 0))
          ((#\S) (if (= len 1) shift-modifier 0))
          ((#\s) (cond
                  ((string=? name "shift") shift-modifier)
                  ((string=? name "super") super-modifier)
                  ((= len 1)               super-modifier)
                  (else 0)))
          ((#\d) (cond
                  ((string=? name "drag")   drag-modifier)
                  ((string=? name "down")   down-modifier)
                  ((string=? name "double") double-modifier)
                  (else 0)))
          ((#\t) (if (string=? name "triple") triple-modifier 0))
          ((#\u) (if (string=? name "up")     up-modifier     0))
          (else 0))))))))

;;;;
;;;; make-ctrl-char  (mirrors keyboard.c:2130–2166)
;;;;

(define (make-ctrl-char c)
  "Apply the control modifier to character C.  Handles ASCII control
   region remapping and the shift bit for upper-case letters."
  (let ((upper (logand c (lognot #o177))))
    (cond
     ;; Non-ASCII: just OR with ctrl-modifier.
     ((> c #x7F)
      (logior c ctrl-modifier))
     (else
      (let* ((c7 (logand c #o177))
             (c-final
              (cond
               ;; Upper-letter region [@..`): map to control char, set shift if A-Z.
               ((and (>= c7 #o100) (< c7 #o140))
                (let ((stripped (logand c7 (lognot #o140))))
                  (if (and (>= c7 (char->integer #\A))
                           (<= c7 (char->integer #\Z)))
                      (logior stripped shift-modifier)
                      stripped)))
               ;; Lower-letter region [a..z]: map to control char.
               ((and (>= c7 (char->integer #\a)) (<= c7 (char->integer #\z)))
                (logand c7 (lognot #o140)))
               ;; Printable: include ctrl-modifier.
               ((>= c7 (char->integer #\space))
                (logior c7 ctrl-modifier))
               (else c7))))
        (logior c-final (logand upper (lognot ctrl-modifier))))))))

;;;;
;;;; event-convert-list  (elisp-callable)
;;;;

(define (event-convert-list event-desc)
  "Convert event description list EVENT-DESC to an event type (character
   or symbol).  EVENT-DESC contains one base event type and zero or more
   modifier names (control, meta, hyper, super, shift, alt, drag, down,
   double, triple).  The base must be last."
  (let loop ((rest event-desc)
             (base #f)
             (have-base? #f)
             (modifiers 0))
    (cond
     ((null? rest)
      (let ((base (cond
                   ;; Single-character symbol → character code.
                   ((and (elisp-symbol? base)
                         (= 1 (string-length (elisp-symbol->string base))))
                    (char->integer (string-ref (elisp-symbol->string base) 0)))
                   (else base))))
        (cond
         ((integer? base)
          ;; (shift a) → A
          (let-values
              (((modifiers base)
                (if (and (not (zero? (logand modifiers shift-modifier)))
                         (>= base (char->integer #\a))
                         (<= base (char->integer #\z)))
                    (values (logand modifiers (lognot shift-modifier))
                            (- base (- (char->integer #\a) (char->integer #\A))))
                    (values modifiers base))))
            ;; (control a) → C-a (via make-ctrl-char)
            (if (not (zero? (logand modifiers ctrl-modifier)))
                (logior (logand modifiers (lognot ctrl-modifier))
                        (make-ctrl-char base))
                (logior modifiers base))))
         ((elisp-symbol? base)
          (apply-modifiers modifiers base))
         (else (error "Invalid base event")))))
     ((not (pair? rest))
      (error "Invalid event description"))
     (else
      (let ((elt (car rest)))
        (cond
         ;; Symbol AND more list to come — try as modifier name.
         ((and (elisp-symbol? elt) (pair? (cdr rest)))
          (let ((this (parse-solitary-modifier elt)))
            (cond
             ((not (zero? this))
              (loop (cdr rest) base have-base? (logior modifiers this)))
             (have-base?
              (error "Two bases given in one event"))
             (else
              (loop (cdr rest) elt #t modifiers)))))
         (else
          (cond
           (have-base?
            (error "Two bases given in one event"))
           (else
            (loop (cdr rest) elt #t modifiers))))))))))

;;;;
;;;; event-symbol-parse-modifiers  (elisp-callable: internal-event-symbol-parse-modifiers)
;;;;

(define (event-symbol-parse-modifiers sym)
  "Parse the event symbol.  Returns the lispier (BASE . MODIFIER-LIST)
   form cached under 'event-symbol-elements (filling caches as needed)."
  (parse-modifiers sym)
  (if (elisp-symbol? sym)
      (plist-get sym event-symbol-elements)
      #nil))

;;;;
;;;; Registration  (elisp-visible names)
;;;;

(define (init-event-modifiers-registrations)
  "Register elisp-callable functions from this module."
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `((event-convert-list                       ,event-convert-list)
              (internal-event-symbol-parse-modifiers    ,event-symbol-parse-modifiers))))
