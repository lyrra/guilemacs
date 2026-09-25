;;; test-m41-imp3.el --- M41 imp-3 (src/xdisp.c thin accessors) suite.
;;;
;;; Pins the M41 imp-3 port (brief.org): the set-buffer-redisplay,
;;; get-display-property, and lookup-image-map decisions move to (emacs
;;; xdisp).  Each DEFUN keeps its name and gets a static C dispatcher;
;;; C computes the mechanism facts and tests the module result.  No C
;;; fallback.
;;;
;;; Wraps test/m41/test-m41-imp3.scm -- the Scheme corpus.  Binds the
;;; repo root as %m41-root, loads the Scheme file via eval-scheme, then
;;; reads back `test-results' (list of (NAME STATUS) pairs).  Each
;;; (NAME PASS|FAIL) pair is reported via princ AND turned into an ERT
;;; test so the harness counts it.  Each (NAME INFO VALUE) pair is
;;; printed as an INFO line and is NOT asserted.  A corpus load error, a
;;; readback error or an empty corpus is reported as a real FAIL (never
;;; a silent 0 failed).
;;;
;;; It adds end-to-end checks that reach the live C DEFUNs, so the C ->
;;; module path runs for real.

(princ "=== m41 imp-3 (src/xdisp.c thin accessors) test suite ===\n")

(require 'imp-ert-report)

(defvar m41-imp3--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defun m41-imp3--check (name ok)
  "Report and register one check.  OK is a boolean."
  (princ (format "%s m41/imp3/%s\n" (if ok "PASS" "FAIL") name))
  (imp-register-bool-as-ert-test (format "m41-imp3/%s" name) ok))

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m41-imp3.scm" dir))
       (load-error nil))
  ;; The corpus reads the build tree, so tell it where the root is.
  (eval-scheme (format "(define %%m41-root %S)" m41-imp3--root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m41-imp3/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m41-imp3/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m41-imp3/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        (cond
         (ok
          (imp-register-check-as-ert-test (format "m41-imp3/%s" name) status)
          (setq pass (1+ pass))
          (princ (format "PASS %s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          (princ (format "INFO %s %s\n" name (cadr status))))
         (t
          (imp-register-check-as-ert-test (format "m41-imp3/%s" name) status)
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result)))))))

    ;; --- End-to-end: the live DEFUNs through the C boundary (cr.org F6) -
    ;; The .scm corpus checks the module return only.  These calls reach
    ;; the C DEFUNs live, so the C -> module path runs for real: the C
    ;; computes the mechanism facts and tests the module result.
    (let ((e2e (lambda (name thunk)
                 (m41-imp3--check name
                                  (condition-case nil (funcall thunk)
                                    (error nil))))))

      ;; get-display-property: read the `display' text property (nil
      ;; PROPERTIES).  The C takes the Fget_text_property branch, then
      ;; find_display_property resolves PROP in the display spec.  A
      ;; string object is safe in batch mode.
      (funcall e2e "e2e/get-display-property/text-prop"
               (lambda ()
                 (let ((s (propertize "abc" 'display '((foo bar)))))
                   (eq (get-display-property 0 'foo s) 'bar))))

      ;; get-display-property: an explicit PROPERTIES list skips the
      ;; text-property read (the else branch: CHECK_LIST + scan).
      (funcall e2e "e2e/get-display-property/properties-list"
               (lambda ()
                 (eq (get-display-property 0 'foo "abc" '((foo bar))) 'bar)))

      ;; get-display-property: a NILP-true but not #nil PROPERTIES (a
      ;; Scheme #f) must still read the `display' text property.  This is
      ;; the cr.org F1 case; the base (NILP-wide) reads the text property.
      (funcall e2e "e2e/get-display-property/nilp-false-prop"
               (lambda ()
                 (let ((s (propertize "abc" 'display '((foo bar)))))
                   (eq (get-display-property 0 'foo s (eval-scheme "#f"))
                       'bar))))

      ;; lookup-image-map: a real map.  The DEFUN lives under
      ;; HAVE_WINDOW_SYSTEM; guard on fboundp.  When the DEFUN is absent
      ;; the check passes (a build with no window system), so the gate
      ;; does not go red on absence (cr.org F3).  An empty map returns
      ;; nil.
      (funcall e2e "e2e/lookup-image-map/empty-nil"
               (lambda ()
                 (or (not (fboundp 'lookup-image-map))
                     (null (lookup-image-map nil 0 0)))))
      (funcall e2e "e2e/lookup-image-map/hit"
               (lambda ()
                 (or (not (fboundp 'lookup-image-map))
                     (let ((map '(((rect . ((0 . 0) . (10 . 10))) id nil))))
                       (equal (lookup-image-map map 5 5) (car map))))))

      ;; lookup-image-map: a NILP-true but not #nil MAP (a Scheme #f)
      ;; must return nil at once, not signal wrong-type-argument.  This
      ;; is the cr.org F1 case.
      (funcall e2e "e2e/lookup-image-map/nilp-false-map"
               (lambda ()
                 (or (not (fboundp 'lookup-image-map))
                     (null (lookup-image-map (eval-scheme "#f") 0 0)))))

      ;; set-buffer-redisplay: a direct call runs the C DEFUN, which
      ;; calls the module and then runs the two slot writes.  It returns
      ;; nil.
      (funcall e2e "e2e/set-buffer-redisplay/nil"
               (lambda ()
                 (with-temp-buffer
                   (null (set-buffer-redisplay nil nil nil nil))))))

    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
