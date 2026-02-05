;; Phase 1 validation tests - uses validate-buffer-local-hash to check
;; C struct fields match hash table at every step

;; Test 1: Fresh buffer creation
(let ((buf (get-buffer-create "v-test1")))
  (validate-buffer-local-hash buf)
  (kill-buffer buf)
  (message "Validate 1 PASS: fresh buffer hash matches struct"))

;; Test 2: After setq-local
(let ((buf (get-buffer-create "v-test2")))
  (with-current-buffer buf
    (setq-local fill-column 42)
    (validate-buffer-local-hash buf)
    (setq-local tab-width 4)
    (validate-buffer-local-hash buf)
    (setq-local truncate-lines t)
    (validate-buffer-local-hash buf))
  (kill-buffer buf)
  (message "Validate 2 PASS: hash matches after setq-local"))

;; Test 3: After let-binding and unwinding
(let ((buf (get-buffer-create "v-test3")))
  (with-current-buffer buf
    (setq-local fill-column 42)
    (validate-buffer-local-hash buf)
    (let ((fill-column 99))
      (validate-buffer-local-hash buf))
    ;; After unwind
    (validate-buffer-local-hash buf))
  (kill-buffer buf)
  (message "Validate 3 PASS: hash matches after let-binding unwind"))

;; Test 4: After kill-all-local-variables
(let ((buf (get-buffer-create "v-test4")))
  (with-current-buffer buf
    (setq-local fill-column 42)
    (setq-local tab-width 8)
    (kill-all-local-variables)
    (validate-buffer-local-hash buf))
  (kill-buffer buf)
  (message "Validate 4 PASS: hash matches after kill-all-local-variables"))

;; Test 5: Multiple buffers simultaneously
(let ((bufs nil))
  (dotimes (i 20)
    (let ((b (get-buffer-create (format "v-multi-%d" i))))
      (push b bufs)
      (with-current-buffer b
        (setq-local fill-column (+ 10 i)))))
  (dolist (b bufs)
    (validate-buffer-local-hash b))
  (mapc #'kill-buffer bufs)
  (message "Validate 5 PASS: 20 buffers all valid"))

;; Test 6: Buffer after various mode operations
(let ((buf (get-buffer-create "v-test6")))
  (with-current-buffer buf
    (fundamental-mode)
    (validate-buffer-local-hash buf))
  (kill-buffer buf)
  (message "Validate 6 PASS: hash matches after fundamental-mode"))

;; Test 7: set-buffer-modified-p (tests bset via C path)
(let ((buf (get-buffer-create "v-test7")))
  (with-current-buffer buf
    (insert "hello")
    (validate-buffer-local-hash buf)
    (set-buffer-modified-p nil)
    (validate-buffer-local-hash buf))
  (kill-buffer buf)
  (message "Validate 7 PASS: hash matches after set-buffer-modified-p"))

(message "All Phase 1 validation tests passed!")
