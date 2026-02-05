;; Phase 3 tests: BVAR now reads from hash table
;; Verify that the hash table is the primary read path.

;; Test 1: Basic BVAR read matches setq-local
(let ((buf (get-buffer-create "p3-test1")))
  (with-current-buffer buf
    (setq-local fill-column 42)
    (unless (= fill-column 42)
      (error "Test 1 FAIL: expected 42, got %s" fill-column))
    ;; Validate hash still matches struct
    (validate-buffer-local-hash buf))
  (kill-buffer buf)
  (message "Test 1 PASS: basic BVAR read after setq-local"))

;; Test 2: Multiple buffers with different values - read via BVAR
(let ((b1 (get-buffer-create "p3-b1"))
      (b2 (get-buffer-create "p3-b2")))
  (with-current-buffer b1
    (setq-local fill-column 11)
    (setq-local tab-width 4))
  (with-current-buffer b2
    (setq-local fill-column 22)
    (setq-local tab-width 8))
  ;; Read from each buffer
  (with-current-buffer b1
    (unless (= fill-column 11) (error "b1 fill-column: expected 11"))
    (unless (= tab-width 4) (error "b1 tab-width: expected 4")))
  (with-current-buffer b2
    (unless (= fill-column 22) (error "b2 fill-column: expected 22"))
    (unless (= tab-width 8) (error "b2 tab-width: expected 8")))
  (kill-buffer b1)
  (kill-buffer b2)
  (message "Test 2 PASS: multiple buffers with different values"))

;; Test 3: let-binding with BVAR read
(let ((buf (get-buffer-create "p3-test3")))
  (with-current-buffer buf
    (setq-local fill-column 42)
    (let ((fill-column 99))
      (unless (= fill-column 99)
        (error "Test 3a: expected 99, got %s" fill-column))
      (validate-buffer-local-hash buf))
    (unless (= fill-column 42)
      (error "Test 3b: expected 42, got %s" fill-column))
    (validate-buffer-local-hash buf))
  (kill-buffer buf)
  (message "Test 3 PASS: let-binding with BVAR read + hash validation"))

;; Test 4: kill-all-local-variables resets correctly
(let ((buf (get-buffer-create "p3-test4")))
  (with-current-buffer buf
    (setq-local fill-column 42)
    (kill-all-local-variables)
    ;; Should read default value (70) via hash
    (unless (= fill-column 70)
      (error "Test 4: expected default 70, got %s" fill-column))
    (validate-buffer-local-hash buf))
  (kill-buffer buf)
  (message "Test 4 PASS: kill-all-local-variables resets hash correctly"))

;; Test 5: Stress test - many buffers, reads via hash
(let ((bufs nil))
  (dotimes (i 100)
    (let ((b (get-buffer-create (format "p3-stress-%d" i))))
      (push b bufs)
      (with-current-buffer b
        (setq-local fill-column (+ 10 i))
        (setq-local tab-width (1+ (mod i 8))))))
  ;; Verify all values
  (let ((i 0))
    (dolist (b (reverse bufs))
      (with-current-buffer b
        (unless (= fill-column (+ 10 i))
          (error "Stress buf %d: fill-column expected %d got %d"
                 i (+ 10 i) fill-column))
        (unless (= tab-width (1+ (mod i 8)))
          (error "Stress buf %d: tab-width expected %d got %d"
                 i (1+ (mod i 8)) tab-width))
        (validate-buffer-local-hash b))
      (setq i (1+ i))))
  (mapc #'kill-buffer bufs)
  (message "Test 5 PASS: 100 buffers stress test with hash reads"))

;; Test 6: Buffer switch during let-binding (correctness of buffer-local semantics)
(let ((b1 (get-buffer-create "p3-switch1"))
      (b2 (get-buffer-create "p3-switch2")))
  (with-current-buffer b1
    (setq-local fill-column 11))
  (with-current-buffer b2
    (setq-local fill-column 22))
  (with-current-buffer b1
    (let ((fill-column 99))
      ;; In b1, should be 99
      (unless (= fill-column 99)
        (error "Test 6a: in b1 during let expected 99, got %s" fill-column))
      (with-current-buffer b2
        ;; In b2, should see b2's value (22), not the let-bound 99
        (unless (= fill-column 22)
          (error "Test 6b: in b2 during let expected 22, got %s" fill-column))))
    ;; After let unwind, b1 should be 11 again
    (unless (= fill-column 11)
      (error "Test 6c: in b1 after let expected 11, got %s" fill-column)))
  (kill-buffer b1)
  (kill-buffer b2)
  (message "Test 6 PASS: buffer switch during let-binding"))

;; Test 7: Rapid bind/unbind cycles with validation
(defvar test-p3-rapid 0)
(dotimes (i 500)
  (let ((test-p3-rapid (1+ i)))
    nil))
(unless (= test-p3-rapid 0)
  (error "Test 7: expected 0 after rapid cycles, got %s" test-p3-rapid))
(message "Test 7 PASS: 500 rapid PLAINVAL bind/unbind cycles")

;; Test 8: Rapid buffer-local bind/unbind cycles with validation
(let ((buf (get-buffer-create "p3-rapid-bl")))
  (with-current-buffer buf
    (setq-local fill-column 42)
    (dotimes (i 500)
      (let ((fill-column (+ 100 i)))
        nil))
    (unless (= fill-column 42)
      (error "Test 8: expected 42 after rapid BL cycles, got %s" fill-column))
    (validate-buffer-local-hash buf))
  (kill-buffer buf)
  (message "Test 8 PASS: 500 rapid buffer-local bind/unbind cycles"))

;; Test 9: Condition-case with buffer-local let
(let ((buf (get-buffer-create "p3-condcase")))
  (with-current-buffer buf
    (setq-local fill-column 42)
    (condition-case nil
        (let ((fill-column 99))
          (error "boom"))
      (error nil))
    (unless (= fill-column 42)
      (error "Test 9: expected 42 after error, got %s" fill-column))
    (validate-buffer-local-hash buf))
  (kill-buffer buf)
  (message "Test 9 PASS: condition-case with buffer-local let"))

;; Test 10: Read buffer name via BVAR (internal field, not DEFVAR_PER_BUFFER - fallback path)
(let ((buf (get-buffer-create "p3-name-test")))
  (unless (string= (buffer-name buf) "p3-name-test")
    (error "Test 10: buffer name mismatch: %s" (buffer-name buf)))
  (kill-buffer buf)
  (message "Test 10 PASS: buffer name read (fallback path for internal fields)"))

(message "All Phase 3 tests passed!")
