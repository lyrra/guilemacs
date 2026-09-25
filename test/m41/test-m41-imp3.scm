;;; test-m41-imp3.scm --- M41 imp-3: the src/xdisp.c thin accessors.
;;;
;;; brief.org (M41 imp-3) moves the *decision* of three src/xdisp.c
;;; DEFUNs into the module (emacs xdisp):
;;;
;;;   set-buffer-redisplay -- the Fset_buffer_redisplay write decision:
;;;                           mark the current buffer for redisplay.
;;;   get-display-property -- the Fget_display_property source
;;;                           decision: read the `display' text property
;;;                           (nil PROPERTIES) or use PROPERTIES.
;;;   lookup-image-map     -- the Flookup_image_map empty-map decision:
;;;                           an empty MAP returns nil at once.
;;;
;;; The mechanism stays C: the bset_update_mode_line call and the two
;;; slot writes, Fget_text_property, CHECK_LIST, find_display_property,
;;; CHECK_FIXNUM, clip_to_bounds, and find_hot_spot.  Each DEFUN stays
;;; C, keeps its elisp name, and calls the module through a static
;;; dispatcher (scm_c_public_ref + SCM_CALL_0/1).  No C fallback.
;;;
;;; Two kinds of check: the decision value on synthetic inputs (the C
;;; rule, computed here independently of the module body spelling), and a
;;; static scan of the module, src/xdisp.c, and the harness registration.
;;;
;;; The repo root is bound by the .el wrapper as %m41-root.  The .el
;;; wrapper turns each (NAME PASS|FAIL) pair into an ERT test; see
;;; test/m41/test-m41-imp3.el.

(use-modules (srfi srfi-13))

(use-modules (emacs xdisp))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

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

(define (repo path) (string-append %m41-root "/" path))

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

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m41-root))
    (begin (report "m41-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m41-root "."))
    (report "m41-root-bound" 'PASS))

;;; --- 1. The module exports the three procedures --------------------
(define xdisp (resolve-module '(emacs xdisp)))
(define sbr (module-ref xdisp 'xdisp-set-buffer-redisplay))
(define gdp (module-ref xdisp 'xdisp-get-display-property-use-text-prop-p))
(define lim (module-ref xdisp 'xdisp-lookup-image-map-empty-p))

(check "m41/imp3/export/xdisp-set-buffer-redisplay" #t
       (procedure? sbr))
(check "m41/imp3/export/xdisp-get-display-property-use-text-prop-p" #t
       (procedure? gdp))
(check "m41/imp3/export/xdisp-lookup-image-map-empty-p" #t
       (procedure? lim))

;;; --- 2. Unit: the decision value on synthetic inputs ---------------
;;; The C rule of set-buffer-redisplay (src/xdisp.c:1047): the current
;;; buffer is always marked for redisplay, so the write decision is t.
(check "m41/imp3/unit/sbr" #t (sbr))

;; The C rule of get-display-property (src/xdisp.c:5979):
;;   if (NILP (properties)) -> read the `display' text property.
;; The C passes PROPERTIES as an elisp value.  The nil test is NILP-wide
;; (#nil, #f, ()), so #f and () also mean "read the text property"
;; (cr.org F1); a non-nil value -> #nil.
(check "m41/imp3/unit/gdp/nil" #t (gdp #nil))
(check "m41/imp3/unit/gdp/false" #t (gdp #f))
(check "m41/imp3/unit/gdp/empty-list" #t (gdp '()))
(check "m41/imp3/unit/gdp/non-nil" #nil (gdp '(foo . bar)))

;; The C rule of lookup-image-map (src/xdisp.c:35764):
;;   if (NILP (map)) -> return Qnil at once.
;; The nil test is NILP-wide (#nil, #f, ()), so #f and () also mean "an
;; empty map" (cr.org F1); a non-nil value -> #nil.
(check "m41/imp3/unit/lim/nil" #t (lim #nil))
(check "m41/imp3/unit/lim/false" #t (lim #f))
(check "m41/imp3/unit/lim/empty-list" #t (lim '()))
(check "m41/imp3/unit/lim/non-nil" #nil (lim '((rect . ((0 . 0) . (1 . 1))))))

;;; --- 3. Static: the module source and the export list -------------
(define xdisp-mod (slurp (repo "mod/emacs/xdisp.scm")))
(check "m41/imp3/module/exists" #t (and (string? xdisp-mod) #t))
(check "m41/imp3/module/export-set-buffer-redisplay" #t
       (contains? xdisp-mod "xdisp-set-buffer-redisplay"))
(check "m41/imp3/module/export-get-display-property" #t
       (contains? xdisp-mod "xdisp-get-display-property-use-text-prop-p"))
(check "m41/imp3/module/export-lookup-image-map" #t
       (contains? xdisp-mod "xdisp-lookup-image-map-empty-p"))
(check "m41/imp3/module/defines-set-buffer-redisplay" #t
       (contains? xdisp-mod "(define (xdisp-set-buffer-redisplay"))
(check "m41/imp3/module/defines-get-display-property" #t
       (contains? xdisp-mod "(define (xdisp-get-display-property-use-text-prop-p"))
(check "m41/imp3/module/defines-lookup-image-map" #t
       (contains? xdisp-mod "(define (xdisp-lookup-image-map-empty-p"))

;; The NILP-width helper: the two imp-3 predicates must keep the C NILP
;; width (#nil, #f, ()) (cr.org F1).  The helper mirrors scm_is_lisp_false.
(check "m41/imp3/module/defines-lisp-false" #t
       (contains? xdisp-mod "(define (%lisp-false? x)"))
(check "m41/imp3/module/gdp-uses-lisp-false" #t
       (contains? xdisp-mod "(if (%lisp-false? properties) #t #nil))"))
(check "m41/imp3/module/lim-uses-lisp-false" #t
       (contains? xdisp-mod "(if (%lisp-false? map) #t #nil))"))

;;; --- 4. Static: the C dispatchers and the three DEFUN bodies ------
(define xdisp-c (slurp (repo "src/xdisp.c")))
(check "m41/imp3/c/xdisp-exists" #t (and (string? xdisp-c) #t))

;; The three new static dispatchers.
(check "m41/imp3/c/dispatcher-set-buffer-redisplay" #t
       (contains? xdisp-c "set_buffer_redisplay_decision"))
(check "m41/imp3/c/dispatcher-get-display-property" #t
       (contains? xdisp-c "get_display_property_decision"))
(check "m41/imp3/c/dispatcher-lookup-image-map" #t
       (contains? xdisp-c "lookup_image_map_decision"))

;; Each dispatcher resolves its module procedure once.
(check "m41/imp3/c/public-ref-set-buffer-redisplay" #t
       (contains? xdisp-c "\"xdisp-set-buffer-redisplay\""))
(check "m41/imp3/c/public-ref-get-display-property" #t
       (contains? xdisp-c "\"xdisp-get-display-property-use-text-prop-p\""))
(check "m41/imp3/c/public-ref-lookup-image-map" #t
       (contains? xdisp-c "\"xdisp-lookup-image-map-empty-p\""))

;; Each DEFUN body is one dispatcher call: the decision moved, no C
;; fallback.
(check "m41/imp3/c/defun-set-buffer-redisplay-calls" #t
       (contains? xdisp-c "if (!NILP (set_buffer_redisplay_decision ()))"))
(check "m41/imp3/c/defun-get-display-property-calls" #t
       (contains? xdisp-c
                  "if (!NILP (get_display_property_decision (properties)))"))
(check "m41/imp3/c/defun-lookup-image-map-calls" #t
       (contains? xdisp-c "if (!NILP (lookup_image_map_decision (map)))"))

;; The old inline decides are gone.
(check "m41/imp3/c/no-inline-nilp-properties" #t
       (if (contains? xdisp-c "if (NILP (properties))") #f #t))
(check "m41/imp3/c/no-inline-nilp-map" #t
       (if (contains? xdisp-c "if (NILP (map))") #f #t))

;; The three DEFUNs stay, with their elisp names (the names still
;; resolve).
(check "m41/imp3/c/defun-set-buffer-redisplay-stays" 1
       (count-lines-starting xdisp-c "DEFUN (\"set-buffer-redisplay\""))
(check "m41/imp3/c/defun-get-display-property-stays" 1
       (count-lines-starting xdisp-c "DEFUN (\"get-display-property\""))
(check "m41/imp3/c/defun-lookup-image-map-stays" 1
       (count-lines-starting xdisp-c "DEFUN (\"lookup-image-map\""))

;; The C keeps the mechanism.
(check "m41/imp3/c/keeps-bset-update-mode-line" #t
       (contains? xdisp-c "bset_update_mode_line (current_buffer)"))
(check "m41/imp3/c/keeps-prevent-redisplay" #t
       (contains? xdisp-c "prevent_redisplay_optimizations_p = true"))
(check "m41/imp3/c/keeps-get-text-property" #t
       (contains? xdisp-c "Fget_text_property (position, Qdisplay, object)"))
(check "m41/imp3/c/keeps-find-display-property" #t
       (contains? xdisp-c "find_display_property (properties, prop)"))
(check "m41/imp3/c/keeps-check-fixnum" #t
       (contains? xdisp-c "CHECK_FIXNUM (x)"))
(check "m41/imp3/c/keeps-clip-to-bounds" #t
       (contains? xdisp-c "clip_to_bounds (INT_MIN, XFIXNUM (x), INT_MAX)"))
(check "m41/imp3/c/keeps-find-hot-spot" #t
       (contains? xdisp-c "find_hot_spot (map,"))

;; The three imp-3 scm_c_public_ref sites land: xdisp.c count 9 -> 12.
(check "m41/imp3/c/xdisp-scm-public-ref-12" 12
       (count-occurrences xdisp-c "scm_c_public_ref"))

;;; --- 5. Static: the harness registers the new corpus --------------
(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m41/imp3/run-tests.scm/group-m41" #t
       (contains? run-tests "(group (m41)"))
(check "m41/imp3/run-tests.scm/registers-el" #t
       (contains? run-tests "test/m41/test-m41-imp3.el"))
