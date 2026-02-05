;; Phase 0 integration tests for per-buffer hash table

;; Test 1: Multiple buffer creation and kill
(let ((bufs (mapcar (lambda (n)
                      (get-buffer-create (format "test-%d" n)))
                    '(1 2 3 4 5))))
  (mapc #'kill-buffer bufs)
  (message "Test 1 PASS: created and killed 5 buffers"))

;; Test 2: Buffer-local variables across switches
(let ((b1 (get-buffer-create "b1"))
      (b2 (get-buffer-create "b2")))
  (with-current-buffer b1
    (setq-local fill-column 42))
  (with-current-buffer b2
    (setq-local fill-column 80))
  (with-current-buffer b1
    (unless (= fill-column 42)
      (error "Expected 42, got %s" fill-column)))
  (with-current-buffer b2
    (unless (= fill-column 80)
      (error "Expected 80, got %s" fill-column)))
  (kill-buffer b1)
  (kill-buffer b2)
  (message "Test 2 PASS: buffer-local values preserved across switches"))

;; Test 3: let-binding of buffer-local with buffer switch
(let ((b1 (get-buffer-create "b1"))
      (b2 (get-buffer-create "b2")))
  (with-current-buffer b1
    (setq-local fill-column 42)
    (let ((fill-column 99))
      (unless (= fill-column 99)
        (error "Expected 99 in let, got %s" fill-column)))
    ;; Back in b1, fill-column should be restored to 42
    (unless (= fill-column 42)
      (error "Expected 42 after let, got %s" fill-column)))
  (kill-buffer b1)
  (kill-buffer b2)
  (message "Test 3 PASS: let-binding with buffer switch"))

;; Test 4: kill-all-local-variables
(let ((buf (get-buffer-create "test-kill-locals")))
  (with-current-buffer buf
    (setq-local fill-column 42)
    (kill-all-local-variables)
    (unless (= fill-column 70)
      (error "Expected default 70, got %s" fill-column)))
  (kill-buffer buf)
  (message "Test 4 PASS: kill-all-local-variables"))

;; Test 5: Many buffers created and killed (stress test)
(let ((bufs nil))
  (dotimes (i 100)
    (push (get-buffer-create (format "stress-%d" i)) bufs))
  (mapc #'kill-buffer bufs)
  (message "Test 5 PASS: stress test 100 buffers"))

;; Test 6: buffer-local-variables returns expected list
(let ((buf (get-buffer-create "test-blv")))
  (with-current-buffer buf
    (setq-local fill-column 42)
    (let ((vars (buffer-local-variables)))
      (unless (assq 'fill-column vars)
        (error "fill-column not in buffer-local-variables"))
      (unless (= (cdr (assq 'fill-column vars)) 42)
        (error "fill-column value wrong in buffer-local-variables"))))
  (kill-buffer buf)
  (message "Test 6 PASS: buffer-local-variables"))

;; Test 7: Multiple buffer-local vars
(let ((buf (get-buffer-create "test-multi")))
  (with-current-buffer buf
    (setq-local fill-column 42)
    (setq-local tab-width 8)
    (setq-local truncate-lines t)
    (unless (= fill-column 42) (error "fill-column wrong"))
    (unless (= tab-width 8) (error "tab-width wrong"))
    (unless truncate-lines (error "truncate-lines wrong")))
  (kill-buffer buf)
  (message "Test 7 PASS: multiple buffer-local vars"))

(message "All Phase 0 tests passed!")
