;; Phase 4 tests: buffer-local bind-symbol goes through hash table
;; Validates that bind-symbol's buffer-local path uses hashq-ref/hashq-set!
;; on the per-buffer hash table, and that all C read paths see the hash values.

;; Test 1: let-binding of a buffer-local variable reads/writes via hash
(let ((buf (get-buffer-create "p4-test1")))
  (with-current-buffer buf
    (setq-local fill-column 42)
    (let ((fill-column 99))
      ;; Inside let: should read 99 (from hash, set by bind-symbol)
      (unless (= fill-column 99)
        (error "Test 1a FAIL: expected 99, got %s" fill-column))
      ;; symbol-value should also see 99 (do_symval_forwarding reads hash)
      (unless (= (symbol-value 'fill-column) 99)
        (error "Test 1b FAIL: symbol-value expected 99, got %s"
               (symbol-value 'fill-column)))
      ;; buffer-local-value should see 99
      (unless (= (buffer-local-value 'fill-column buf) 99)
        (error "Test 1c FAIL: buffer-local-value expected 99, got %s"
               (buffer-local-value 'fill-column buf))))
    ;; After let: should be restored to 42
    (unless (= fill-column 42)
      (error "Test 1d FAIL: expected 42 after let, got %s" fill-column))
    (unless (= (symbol-value 'fill-column) 42)
      (error "Test 1e FAIL: symbol-value expected 42 after let, got %s"
             (symbol-value 'fill-column))))
  (kill-buffer buf)
  (message "Test 1 PASS: let-binding reads/writes via hash"))

;; Test 2: buffer-local hash stays in sync with struct during let-binding
;; (write-through to the C slot mirror; see buffer-local-let-set!)
(let ((buf (get-buffer-create "p4-test2")))
  (with-current-buffer buf
    (setq-local fill-column 42)
    ;; Before let: hash and struct should be in sync (0 mismatches)
    (let ((m (validate-buffer-local-hash buf)))
      (unless (= m 0)
        (error "Test 2a FAIL: expected 0 mismatches before let, got %d" m)))
    (let ((fill-column 99))
      ;; During let: hash AND struct both have 99 -> in sync
      (let ((m (validate-buffer-local-hash buf)))
        (unless (= m 0)
          (error "Test 2b FAIL: expected 0 mismatches during let, got %d" m))))
    ;; After let: should be back in sync
    (let ((m (validate-buffer-local-hash buf)))
      (unless (= m 0)
        (error "Test 2c FAIL: expected 0 mismatches after let, got %d" m))))
  (kill-buffer buf)
  (message "Test 2 PASS: hash/struct in sync during and after let"))

;; Test 3: buffer-local-hash returns the hash table object
(let ((buf (get-buffer-create "p4-test3")))
  (with-current-buffer buf
    (let ((h (buffer-local-hash)))
      (unless h
        (error "Test 3a FAIL: buffer-local-hash returned nil"))
      ;; It should be truthy (a hash table)
      (unless (not (null h))
        (error "Test 3b FAIL: hash table is null"))))
  (kill-buffer buf)
  (message "Test 3 PASS: buffer-local-hash returns hash table"))

;; Test 4: buffer switch during let-binding - bind restores to original buffer
(let ((b1 (get-buffer-create "p4-switch1"))
      (b2 (get-buffer-create "p4-switch2")))
  (with-current-buffer b1
    (setq-local fill-column 11))
  (with-current-buffer b2
    (setq-local fill-column 22))
  (with-current-buffer b1
    (let ((fill-column 99))
      ;; In b1: should be 99
      (unless (= fill-column 99)
        (error "Test 4a FAIL: b1 during let expected 99, got %s" fill-column))
      (with-current-buffer b2
        ;; In b2: should see b2's value (22), NOT the let-bound 99
        (unless (= fill-column 22)
          (error "Test 4b FAIL: b2 during let expected 22, got %s" fill-column))
        ;; symbol-value in b2 should also be 22
        (unless (= (symbol-value 'fill-column) 22)
          (error "Test 4c FAIL: symbol-value in b2 expected 22, got %s"
                 (symbol-value 'fill-column)))))
    ;; After let unwind: b1 should be 11 again
    (unless (= fill-column 11)
      (error "Test 4d FAIL: b1 after let expected 11, got %s" fill-column)))
  (kill-buffer b1)
  (kill-buffer b2)
  (message "Test 4 PASS: buffer switch during let-binding"))

;; Test 5: nested let-bindings of buffer-local variable
(let ((buf (get-buffer-create "p4-test5")))
  (with-current-buffer buf
    (setq-local fill-column 10)
    (let ((fill-column 20))
      (unless (= fill-column 20)
        (error "Test 5a FAIL: outer let expected 20"))
      (let ((fill-column 30))
        (unless (= fill-column 30)
          (error "Test 5b FAIL: inner let expected 30")))
      (unless (= fill-column 20)
        (error "Test 5c FAIL: back to outer let expected 20")))
    (unless (= fill-column 10)
      (error "Test 5d FAIL: after all lets expected 10")))
  (kill-buffer buf)
  (message "Test 5 PASS: nested let-bindings of buffer-local"))

;; Test 6: condition-case with buffer-local let via hash path
(let ((buf (get-buffer-create "p4-test6")))
  (with-current-buffer buf
    (setq-local fill-column 42)
    (condition-case nil
        (let ((fill-column 99))
          (error "boom"))
      (error nil))
    (unless (= fill-column 42)
      (error "Test 6 FAIL: expected 42 after error, got %s" fill-column))
    ;; Verify hash and struct are back in sync
    (let ((m (validate-buffer-local-hash buf)))
      (unless (= m 0)
        (error "Test 6b FAIL: expected 0 mismatches after error unwind, got %d" m))))
  (kill-buffer buf)
  (message "Test 6 PASS: condition-case unwind via hash path"))

;; Test 7: rapid buffer-local let cycles via hash path
(let ((buf (get-buffer-create "p4-rapid")))
  (with-current-buffer buf
    (setq-local fill-column 42)
    (dotimes (i 1000)
      (let ((fill-column (+ 100 i)))
        nil))
    (unless (= fill-column 42)
      (error "Test 7 FAIL: expected 42 after 1000 cycles, got %s" fill-column))
    (let ((m (validate-buffer-local-hash buf)))
      (unless (= m 0)
        (error "Test 7b FAIL: expected 0 mismatches after cycles, got %d" m))))
  (kill-buffer buf)
  (message "Test 7 PASS: 1000 rapid buffer-local let cycles via hash"))

;; Test 8: multiple buffer-local vars bound simultaneously
(let ((buf (get-buffer-create "p4-test8")))
  (with-current-buffer buf
    (setq-local fill-column 40)
    (setq-local tab-width 4)
    (let ((fill-column 80)
          (tab-width 8))
      (unless (= fill-column 80)
        (error "Test 8a FAIL: fill-column expected 80"))
      (unless (= tab-width 8)
        (error "Test 8b FAIL: tab-width expected 8")))
    (unless (= fill-column 40)
      (error "Test 8c FAIL: fill-column expected 40 after let"))
    (unless (= tab-width 4)
      (error "Test 8d FAIL: tab-width expected 4 after let")))
  (kill-buffer buf)
  (message "Test 8 PASS: multiple buffer-local vars bound simultaneously"))

;; Test 9: setq inside let of buffer-local (modifies hash, not struct)
(let ((buf (get-buffer-create "p4-test9")))
  (with-current-buffer buf
    (setq-local fill-column 42)
    (let ((fill-column 99))
      ;; setq modifies the current binding (which is in the hash)
      (setq fill-column 123)
      (unless (= fill-column 123)
        (error "Test 9a FAIL: setq inside let expected 123, got %s" fill-column))
      (unless (= (symbol-value 'fill-column) 123)
        (error "Test 9b FAIL: symbol-value expected 123 after setq")))
    ;; After let unwind: should be back to 42 (the saved old value)
    (unless (= fill-column 42)
      (error "Test 9c FAIL: expected 42 after let unwind, got %s" fill-column)))
  (kill-buffer buf)
  (message "Test 9 PASS: setq inside let of buffer-local"))

;; Test 10: PLAINVAL binding still works (fast path unchanged)
(defvar test-p4-plain 0)
(let ((test-p4-plain 42))
  (unless (= test-p4-plain 42)
    (error "Test 10a FAIL: PLAINVAL let expected 42"))
  (let ((test-p4-plain 99))
    (unless (= test-p4-plain 99)
      (error "Test 10b FAIL: nested PLAINVAL let expected 99")))
  (unless (= test-p4-plain 42)
    (error "Test 10c FAIL: back to outer PLAINVAL expected 42")))
(unless (= test-p4-plain 0)
  (error "Test 10d FAIL: after all lets PLAINVAL expected 0"))
(message "Test 10 PASS: PLAINVAL binding (fast path) unchanged")

;; Test 11: Stress test - many buffers, let-bindings via hash
(let ((bufs nil))
  (dotimes (i 50)
    (let ((b (get-buffer-create (format "p4-stress-%d" i))))
      (push b bufs)
      (with-current-buffer b
        (setq-local fill-column (+ 10 i)))))
  ;; Let-bind fill-column in each buffer and verify
  (let ((i 0))
    (dolist (b (reverse bufs))
      (with-current-buffer b
        (let ((fill-column (+ 1000 i)))
          (unless (= fill-column (+ 1000 i))
            (error "Stress let buf %d: expected %d got %d"
                   i (+ 1000 i) fill-column)))
        ;; After let: should be back to original
        (unless (= fill-column (+ 10 i))
          (error "Stress after-let buf %d: expected %d got %d"
                 i (+ 10 i) fill-column)))
      (setq i (1+ i))))
  (mapc #'kill-buffer bufs)
  (message "Test 11 PASS: 50 buffers let-binding stress test"))

(message "All Phase 4 tests passed!")

;; Test 12: regression - let-bound DEFVAR_PER_BUFFER value survives
;; kill-all-local-variables (custom-make-dependencies / cus-load.el bug)
(let ((buf (get-buffer-create "p4-kill-let")))
  (with-current-buffer buf
    (let ((default-directory "/definitely/not/a/real/dir/"))
      (kill-all-local-variables)
      (unless (equal default-directory "/definitely/not/a/real/dir/")
        (error "Test 12a FAIL: let-bound default-directory lost after kill, got %S"
               default-directory))))
  (kill-buffer buf)
  (message "Test 12 PASS: let-bound default-directory survives kill-all-local-variables"))

;; Test 13: regression - let body killing its own buffer must not error on unwind
(let ((buf (get-buffer-create "p4-kill-body")))
  (condition-case nil
      (with-current-buffer buf
        (let ((default-directory "/definitely/not/a/real/dir/"))
          (kill-buffer (current-buffer))))
    (error (error "Test 13 FAIL: killing bind buffer inside let errored on unwind")))
  (message "Test 13 PASS: killed bind buffer inside let unwinds cleanly"))
