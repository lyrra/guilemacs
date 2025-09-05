;;; test-basic-migration.el --- Test basic comparison and utility functions

;; Test the newly migrated eq, equal, eql, atom, characterp functions

;; Test eq function
(message "Testing eq:")
(message "  (eq 'a 'a) => %s" (eq 'a 'a))         ; should be t
(message "  (eq 1 1) => %s" (eq 1 1))             ; should be t
(message "  (eq 'a 'b) => %s" (eq 'a 'b))         ; should be nil
(message "  (eq '(a) '(a)) => %s" (eq '(a) '(a))) ; should be nil (different objects)

;; Test atom function
(message "Testing atom:")
(message "  (atom 'a) => %s" (atom 'a))           ; should be t
(message "  (atom 42) => %s" (atom 42))           ; should be t
(message "  (atom nil) => %s" (atom nil))         ; should be t
(message "  (atom '(a b)) => %s" (atom '(a b)))   ; should be nil

;; Test equal function
(message "Testing equal:")
(message "  (equal 'a 'a) => %s" (equal 'a 'a))         ; should be t
(message "  (equal 1 1) => %s" (equal 1 1))             ; should be t
(message "  (equal '(a b) '(a b)) => %s" (equal '(a b) '(a b))) ; should be t
(message "  (equal \"hello\" \"hello\") => %s" (equal "hello" "hello")) ; should be t
(message "  (equal 'a 'b) => %s" (equal 'a 'b))         ; should be nil

;; Test eql function
(message "Testing eql:")
(message "  (eql 1 1) => %s" (eql 1 1))               ; should be t
(message "  (eql 1.0 1.0) => %s" (eql 1.0 1.0))       ; should be t
(message "  (eql 'a 'a) => %s" (eql 'a 'a))           ; should be t
(message "  (eql 1 1.0) => %s" (eql 1 1.0))           ; should be nil

;; Test characterp function
(message "Testing characterp:")
(message "  (characterp ?a) => %s" (characterp ?a))    ; should be t
(message "  (characterp 65) => %s" (characterp 65))    ; should be t (character code)
(message "  (characterp 'a) => %s" (characterp 'a))    ; should be nil
(message "  (characterp \"a\") => %s" (characterp "a")) ; should be nil

;; Test newly migrated type predicates
(message "Testing integerp:")
(message "  (integerp 42) => %s" (integerp 42))         ; should be t
(message "  (integerp 1.5) => %s" (integerp 1.5))       ; should be nil
(message "  (integerp 'a) => %s" (integerp 'a))         ; should be nil

(message "Testing recordp:")
(message "  (recordp 'a) => %s" (recordp 'a))           ; should be nil
(message "  (recordp 42) => %s" (recordp 42))           ; should be nil

(message "Testing threadp:")
(message "  (threadp 'a) => %s" (threadp 'a))           ; should be nil

(message "Testing mutexp:")
(message "  (mutexp 'a) => %s" (mutexp 'a))             ; should be nil

(message "Testing condition-variable-p:")
(message "  (condition-variable-p 'a) => %s" (condition-variable-p 'a)) ; should be nil

;; Test basic list access functions
(message "Testing car:")
(message "  (car '(a b c)) => %s" (car '(a b c)))       ; should be a
(message "  (car nil) => %s" (car nil))                 ; should be nil
(message "  (car '()) => %s" (car '()))                 ; should be nil

(message "Testing cdr:")
(message "  (cdr '(a b c)) => %s" (cdr '(a b c)))       ; should be (b c)
(message "  (cdr nil) => %s" (cdr nil))                 ; should be nil
(message "  (cdr '()) => %s" (cdr '()))                 ; should be nil

(message "Testing car-safe:")
(message "  (car-safe '(a b c)) => %s" (car-safe '(a b c))) ; should be a
(message "  (car-safe 'not-a-list) => %s" (car-safe 'not-a-list)) ; should be nil

(message "Testing cdr-safe:")
(message "  (cdr-safe '(a b c)) => %s" (cdr-safe '(a b c))) ; should be (b c)
(message "  (cdr-safe 'not-a-list) => %s" (cdr-safe 'not-a-list)) ; should be nil

;; Test newly migrated utility functions
(message "Testing identity:")
(message "  (identity 'a) => %s" (identity 'a))           ; should be a
(message "  (identity 42) => %s" (identity 42))           ; should be 42
(message "  (identity nil) => %s" (identity nil))         ; should be nil
(message "  (identity \"hello\") => %s" (identity "hello")) ; should be "hello"

(message "Testing bare-symbol-p:")
(message "  (bare-symbol-p 'a) => %s" (bare-symbol-p 'a)) ; should be t
(message "  (bare-symbol-p 42) => %s" (bare-symbol-p 42)) ; should be nil
(message "  (bare-symbol-p \"a\") => %s" (bare-symbol-p "a")) ; should be nil

(message "Testing symbol-with-pos-p:")
(message "  (symbol-with-pos-p 'a) => %s" (symbol-with-pos-p 'a)) ; should be nil
(message "  (symbol-with-pos-p 42) => %s" (symbol-with-pos-p 42)) ; should be nil

(message "Testing bufferp:")
(message "  (bufferp 'a) => %s" (bufferp 'a))             ; should be nil
(message "  (bufferp 42) => %s" (bufferp 42))             ; should be nil

(message "Testing user-ptrp:")
(message "  (user-ptrp 'a) => %s" (user-ptrp 'a))         ; should be nil
(message "  (user-ptrp 42) => %s" (user-ptrp 42))         ; should be nil

(message "All basic function tests completed.")