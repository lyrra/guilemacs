;;; test-buffer-locals.el --- Test Scheme buffer accessor replacements (SRFI-64 style)
;;;
;;; Tests for the Scheme functions in mod/emacs/buffer-locals.scm that
;;; replace C DEFUNs: buffer-name, buffer-file-name, buffer-last-name,
;;; mark-marker, bobp, eobp, current-local-map, syntax-table,
;;; category-table, current-case-table, get-file-buffer,
;;; get-truename-buffer, find-buffer.

(test-begin "buffer-locals")

;;; --- buffer-name ---

(let ((buf (get-buffer-create "p5-test-name")))
  (test-equal "buffer-name/with-arg" "p5-test-name" (buffer-name buf))
  (with-current-buffer buf
    (test-equal "buffer-name/no-arg" "p5-test-name" (buffer-name)))
  (kill-buffer buf))

(let ((buf (get-buffer-create "p5-killed")))
  (kill-buffer buf)
  (test-nil "buffer-name/killed-buffer" (buffer-name buf)))

;;; --- buffer-file-name ---

(let ((buf (get-buffer-create "p5-test-nofile")))
  (test-nil "buffer-file-name/non-file-with-arg" (buffer-file-name buf))
  (with-current-buffer buf
    (test-nil "buffer-file-name/non-file-no-arg" (buffer-file-name)))
  (kill-buffer buf))

(let ((tmpfile (make-temp-file "p5-test-fname")))
  (unwind-protect
      (let ((buf (find-file-noselect tmpfile)))
        (test-equal "buffer-file-name/visiting-with-arg" tmpfile
                    (buffer-file-name buf))
        (with-current-buffer buf
          (test-equal "buffer-file-name/visiting-no-arg" tmpfile
                      (buffer-file-name)))
        (kill-buffer buf))
    (delete-file tmpfile)))

;;; --- buffer-last-name ---

(let ((buf (get-buffer-create "p5-orig-name")))
  (with-current-buffer buf
    (rename-buffer "p5-new-name")
    (test-equal "buffer-last-name/after-rename" "p5-orig-name"
                (buffer-last-name))
    (test-equal "buffer-name/after-rename" "p5-new-name"
                (buffer-name)))
  (kill-buffer buf))

;;; --- mark-marker ---

(let ((buf (get-buffer-create "p5-test-mark")))
  (with-current-buffer buf
    (test-assert "mark-marker/is-marker" (markerp (mark-marker)))
    (insert "hello world")
    (push-mark 5 t t)
    (test-equal "mark-marker/position" 5
                (marker-position (mark-marker))))
  (kill-buffer buf))

;;; --- bobp / eobp ---

(let ((buf (get-buffer-create "p5-test-boe")))
  (with-current-buffer buf
    (erase-buffer)
    ;; Empty buffer: point is at both beginning and end.
    (test-assert "bobp/empty-buffer" (bobp))
    (test-assert "eobp/empty-buffer" (eobp))
    ;; With text.
    (insert "hello world")
    (goto-char (point-min))
    (test-assert "bobp/at-point-min" (bobp))
    (test-nil "eobp/at-point-min" (eobp))
    (goto-char (point-max))
    (test-nil "bobp/at-point-max" (bobp))
    (test-assert "eobp/at-point-max" (eobp)))
  (kill-buffer buf))

;;; --- hash sync after setq-local ---

(let ((buf (get-buffer-create "p5-test-sync")))
  (with-current-buffer buf
    (setq-local fill-column 99)
    (test-equal "hash-sync/buffer-name-after-setq-local" "p5-test-sync"
                (buffer-name))
    (test-equal "hash-sync/validate-hash" 0
                (validate-buffer-local-hash buf)))
  (kill-buffer buf))

;;; --- hash sync during let-binding ---

(let ((buf (get-buffer-create "p5-test-let")))
  (with-current-buffer buf
    (setq-local fill-column 42)
    (let ((fill-column 99))
      (test-equal "let-binding/buffer-name-during" "p5-test-let"
                  (buffer-name)))
    (test-equal "let-binding/buffer-name-after" "p5-test-let"
                (buffer-name)))
  (kill-buffer buf))

;;; --- phase 4 regression (let-binding via hash) ---

(let ((buf (get-buffer-create "p5-regression")))
  (with-current-buffer buf
    (setq-local fill-column 42)
    (let ((fill-column 99))
      (test-equal "regression/let-bound-value" 99 fill-column)
      (test-equal "regression/symbol-value" 99 (symbol-value 'fill-column)))
    (test-equal "regression/after-unwind" 42 fill-column))
  (kill-buffer buf))

;;; --- current-local-map ---

(let ((buf (get-buffer-create "p5-test-keymap")))
  (with-current-buffer buf
    (test-assert "current-local-map/nil-or-keymap"
                 (let ((m (current-local-map)))
                   (or (null m) (keymapp m))))
    (use-local-map (make-sparse-keymap))
    (test-assert "current-local-map/after-use-local-map"
                 (keymapp (current-local-map))))
  (kill-buffer buf))

;;; --- syntax-table ---

(let ((buf (get-buffer-create "p5-test-syntax")))
  (with-current-buffer buf
    (test-assert "syntax-table/is-char-table"
                 (char-table-p (syntax-table))))
  (kill-buffer buf))

;;; Regression: set-syntax-table must sync to the per-buffer hash so that
;;; the Scheme (syntax-table) accessor returns the *same* table object.
;;; Without BVAR_HASH_SYNC in bset_syntax_table, (syntax-table) returns
;;; the stale previous table — which broke f90-mode and any mode that
;;; relies on syntax-table identity after set-syntax-table.

(with-temp-buffer
  (let ((custom (make-syntax-table)))
    (set-syntax-table custom)
    (test-eq "syntax-table/identity-after-set"
             custom (syntax-table))))

(with-temp-buffer
  (let ((t1 (make-syntax-table))
        (t2 (make-syntax-table)))
    (set-syntax-table t1)
    (test-eq "syntax-table/first-set" t1 (syntax-table))
    (set-syntax-table t2)
    (test-eq "syntax-table/second-set" t2 (syntax-table))))

;;; --- category-table ---

(let ((buf (get-buffer-create "p5-test-category")))
  (with-current-buffer buf
    (test-assert "category-table/is-char-table"
                 (char-table-p (category-table))))
  (kill-buffer buf))

;;; Regression: set-category-table must sync to the per-buffer hash,
;;; same issue as syntax-table above.

(with-temp-buffer
  (let ((custom (make-category-table)))
    (set-category-table custom)
    (test-eq "category-table/identity-after-set"
             custom (category-table))))

(with-temp-buffer
  (let ((t1 (make-category-table))
        (t2 (make-category-table)))
    (set-category-table t1)
    (test-eq "category-table/first-set" t1 (category-table))
    (set-category-table t2)
    (test-eq "category-table/second-set" t2 (category-table))))

;;; --- current-case-table ---

(let ((buf (get-buffer-create "p5-test-case")))
  (with-current-buffer buf
    (test-assert "current-case-table/is-char-table"
                 (char-table-p (current-case-table))))
  (kill-buffer buf))

;;; --- case-table in keymap context (exercises BVAR path in keymap.c) ---

; test is disabled, too slow
'(let ((buf (get-buffer-create "p5-test-case-keymap")))
  (with-current-buffer buf
    (let ((map (make-sparse-keymap)))
      (define-key map [menu-bar test] (cons "Test" (make-sparse-keymap)))
      (define-key map [menu-bar test foo-bar] '("Foo" . ignore))
      (use-local-map map)
      (test-assert "case-table-keymap/is-char-table"
                   (char-table-p (current-case-table)))
      (test-eq "case-table-keymap/stable-identity"
               (current-case-table) (current-case-table))))
  (kill-buffer buf))

;;; --- get-file-buffer ---

(let ((tmpfile (make-temp-file "p5-test-gfb")))
  (unwind-protect
      (progn
        (test-nil "get-file-buffer/before-visit"
                  (get-file-buffer tmpfile))
        (let ((buf (find-file-noselect tmpfile)))
          (test-eq "get-file-buffer/finds-visiting-buffer"
                   buf (get-file-buffer tmpfile))
          (test-eq "get-file-buffer/expands-filename"
                   buf (get-file-buffer (concat tmpfile "/.")))
          (kill-buffer buf))
        (test-nil "get-file-buffer/after-kill"
                  (get-file-buffer tmpfile)))
    (delete-file tmpfile)))

;;; --- get-truename-buffer ---

(let ((tmpfile (make-temp-file "p5-test-gtb")))
  (unwind-protect
      (let ((buf (find-file-noselect tmpfile)))
        (let ((truename (file-truename tmpfile)))
          (test-eq "get-truename-buffer/finds-buffer"
                   buf (get-truename-buffer truename))
          (test-nil "get-truename-buffer/nonexistent-path"
                    (get-truename-buffer "/nonexistent/file/path")))
        (kill-buffer buf))
    (delete-file tmpfile)))

;;; --- find-buffer ---

(defvar p5--find-buffer-var nil "Test variable for find-buffer tests.")
(let ((buf1 (get-buffer-create "p5-test-fb-a"))
      (buf2 (get-buffer-create "p5-test-fb-b")))
  (with-current-buffer buf1
    (setq-local p5--find-buffer-var 'alpha))
  (with-current-buffer buf2
    (setq-local p5--find-buffer-var 'beta))
  (test-eq "find-buffer/finds-alpha" buf1
           (find-buffer 'p5--find-buffer-var 'alpha))
  (test-eq "find-buffer/finds-beta" buf2
           (find-buffer 'p5--find-buffer-var 'beta))
  (test-nil "find-buffer/no-match"
            (find-buffer 'p5--find-buffer-var 'gamma))
  (kill-buffer buf1)
  (kill-buffer buf2))

;;; --- bind-symbol PLAINVAL→LOCALIZED transition ---
;;; Regression test: if make-local-variable is called during a let body,
;;; bind-symbol's fast-path unwind must not overwrite the BLV pointer.
;;; Without the fix this crashes (scm_to_pointer on a non-pointer).

(defvar p5--mlv-var "" "Test var with empty-string default.")
(let ((p5--mlv-var nil))
  (with-temp-buffer
    (make-local-variable 'p5--mlv-var)
    (setq p5--mlv-var "local")))
(test-equal "bind-symbol/plainval-to-localized" "" p5--mlv-var)

(defvar p5--mlv-var2 "initial" "Test var for PLAINVAL→LOCALIZED.")
(let ((p5--mlv-var2 nil))
  (with-temp-buffer
    (make-local-variable 'p5--mlv-var2)
    (setq p5--mlv-var2 "local")))
(test-equal "bind-symbol/plainval-to-localized-string" "initial" p5--mlv-var2)

;;; --- bind-symbol let-default path (SPECPDL_LET_DEFAULT) ---
;;; Regression: when let-binding a buffer-local-capable variable that
;;; has NO local value, bind-symbol must save/restore the DEFAULT value
;;; (like C's SPECPDL_LET_DEFAULT).  Otherwise kill-all-local-variables
;;; (called by every major mode switch) destroys the let-bound value.
;;; This broke indent-sexp and 20 other lisp-mode-tests.

(with-temp-buffer
  (let ((indent-tabs-mode nil))
    (kill-all-local-variables)
    (test-assert "let-default/survives-kill-all-local-variables"
                 (not indent-tabs-mode))))

(with-temp-buffer
  (let ((indent-tabs-mode nil))
    (fundamental-mode)
    (test-assert "let-default/survives-mode-switch"
                 (not indent-tabs-mode))))

;;; --- buffer-modified-p (Scheme implementation) ---

(with-temp-buffer
  (test-nil "buffer-modified-p/new-buffer" (buffer-modified-p)))

(with-temp-buffer
  (insert "hello")
  (test-assert "buffer-modified-p/after-insert" (buffer-modified-p)))

(let ((buf (get-buffer-create "p5-test-modified")))
  (with-current-buffer buf
    (insert "hello"))
  (test-assert "buffer-modified-p/with-arg" (buffer-modified-p buf))
  (kill-buffer buf))

(with-temp-buffer
  (insert "hello")
  (set-buffer-modified-p nil)
  (test-nil "buffer-modified-p/after-clear" (buffer-modified-p)))

;;; --- buffer-save-modiff primitive ---

(with-temp-buffer
  (test-assert "buffer-save-modiff/initial-equals-modiff"
               (= (buffer-save-modiff) (buffer-modified-tick)))
  (insert "hello")
  (test-assert "buffer-save-modiff/after-insert-differs"
               (not (= (buffer-save-modiff) (buffer-modified-tick)))))

;;; --- bolp / eolp (Scheme implementation) ---

(with-temp-buffer
  ;; Empty buffer: at both beginning and end of line
  (test-assert "bolp/empty-buffer" (bolp))
  (test-assert "eolp/empty-buffer" (eolp)))

(with-temp-buffer
  (insert "hello\nworld")
  (goto-char (point-min))
  (test-assert "bolp/at-bol" (bolp))
  (test-nil "eolp/at-bol" (eolp))
  (end-of-line)
  (test-nil "bolp/at-eol" (bolp))
  (test-assert "eolp/at-eol" (eolp))
  (forward-char)  ;; move past newline to beginning of second line
  (test-assert "bolp/after-newline" (bolp))
  (test-nil "eolp/after-newline" (eolp))
  (goto-char (point-max))
  (test-nil "bolp/at-point-max" (bolp))
  (test-assert "eolp/at-point-max" (eolp)))

;;; --- stress test ---

(let ((bufs nil))
  (dotimes (i 50)
    (push (get-buffer-create (format "p5-stress-%d" i)) bufs))
  (setq bufs (nreverse bufs))
  (let ((all-ok t)
        (i 0))
    (dolist (b bufs)
      (unless (string= (buffer-name b) (format "p5-stress-%d" i))
        (setq all-ok nil))
      (with-current-buffer b
        (unless (and (bobp) (eobp) (markerp (mark-marker)))
          (setq all-ok nil)))
      (setq i (1+ i)))
    (test-assert "stress/50-buffers-all-accessors" all-ok))
  (mapc #'kill-buffer bufs))

(test-end)
