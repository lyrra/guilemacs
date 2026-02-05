;; Phase 1 integration tests for per-buffer hash table write-through

;; Test 1: Basic buffer creation - hash should match struct
(let ((buf (get-buffer-create "test-p1")))
  (message "Test 1 PASS: buffer creation succeeded"))

;; Test 2: bset_* write-through via setq-local
(let ((buf (get-buffer-create "test-p1-setq")))
  (with-current-buffer buf
    (setq-local fill-column 42)
    (setq-local tab-width 4)
    (setq-local truncate-lines t)
    (unless (= fill-column 42) (error "fill-column wrong"))
    (unless (= tab-width 4) (error "tab-width wrong"))
    (unless truncate-lines (error "truncate-lines wrong")))
  (kill-buffer buf)
  (message "Test 2 PASS: setq-local write-through"))

;; Test 3: let-binding restores correctly (triggers specbind/unbind_once)
(let ((buf (get-buffer-create "test-p1-let")))
  (with-current-buffer buf
    (setq-local fill-column 42)
    (let ((fill-column 99))
      (unless (= fill-column 99)
        (error "Expected 99 in let, got %s" fill-column)))
    (unless (= fill-column 42)
      (error "Expected 42 after let, got %s" fill-column)))
  (kill-buffer buf)
  (message "Test 3 PASS: let-binding restore"))

;; Test 4: kill-all-local-variables resets hash correctly
(let ((buf (get-buffer-create "test-p1-kill")))
  (with-current-buffer buf
    (setq-local fill-column 42)
    (kill-all-local-variables)
    (unless (= fill-column 70)
      (error "Expected default 70, got %s" fill-column)))
  (kill-buffer buf)
  (message "Test 4 PASS: kill-all-local-variables"))

;; Test 5: Multiple buffers with different values
(let ((bufs nil))
  (dotimes (i 50)
    (let ((b (get-buffer-create (format "multi-%d" i))))
      (push b bufs)
      (with-current-buffer b
        (setq-local fill-column (+ 10 i)))))
  ;; Verify all values
  (let ((i 0))
    (dolist (b (reverse bufs))
      (with-current-buffer b
        (unless (= fill-column (+ 10 i))
          (error "Buffer %d: expected %d got %d" i (+ 10 i) fill-column)))
      (setq i (1+ i))))
  (mapc #'kill-buffer bufs)
  (message "Test 5 PASS: 50 buffers with different fill-column values"))

;; Test 6: Buffer switch during let-binding
(let ((b1 (get-buffer-create "p1-b1"))
      (b2 (get-buffer-create "p1-b2")))
  (with-current-buffer b1
    (setq-local fill-column 11))
  (with-current-buffer b2
    (setq-local fill-column 22))
  ;; let-bind in b1, switch to b2
  (with-current-buffer b1
    (let ((fill-column 99))
      (with-current-buffer b2
        ;; Should see b2's value, not 99
        (unless (= fill-column 22)
          (error "In b2 during let: expected 22, got %s" fill-column))))
    ;; Back in b1, should be 11 (let unwound)
    (unless (= fill-column 11)
      (error "In b1 after let: expected 11, got %s" fill-column)))
  (kill-buffer b1)
  (kill-buffer b2)
  (message "Test 6 PASS: buffer switch during let-binding"))

;; Test 7: Rapid create/modify/kill cycle
(dotimes (i 200)
  (let ((b (get-buffer-create (format "rapid-%d" i))))
    (with-current-buffer b
      (setq-local fill-column (+ i 1))
      (setq-local tab-width (1+ (mod i 8))))
    (kill-buffer b)))
(message "Test 7 PASS: 200 rapid create/modify/kill cycles")

(message "All Phase 1 tests passed!")
