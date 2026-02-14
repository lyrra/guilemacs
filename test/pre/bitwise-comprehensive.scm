;;;; comprehensive bitwise operations tests
;;;; testing logical operations, shifts, and bit manipulation
;;;; focus on edge cases, large numbers, and boundary conditions

(use-modules (rnrs arithmetic fixnums))

;;; Basic bitwise operations with small numbers
(deftest logand-basic (2)
  (el-expr `(print (logand 6 3))))

(deftest logior-basic (7)
  (el-expr `(print (logior 4 3))))

(deftest logxor-basic (5)
  (el-expr `(print (logxor 6 3))))

(deftest lognot-basic (-7)
  (el-expr `(print (lognot 6))))

;;; Bitwise operations with zero
(deftest logand-zero (0)
  (el-expr `(print (logand 42 0))))

(deftest logior-zero (42)
  (el-expr `(print (logior 42 0))))

(deftest logxor-zero (42)
  (el-expr `(print (logxor 42 0))))

(deftest logand-with-self (42)
  (el-expr `(print (logand 42 42))))

(deftest logxor-with-self (0)
  (el-expr `(print (logxor 42 42))))

;;; Bitwise operations with -1 (all bits set)
(deftest logand-minus-one (42)
  (el-expr `(print (logand 42 -1))))

(deftest logior-minus-one (-1)
  (el-expr `(print (logior 42 -1))))

(deftest logxor-minus-one (-43)
  (el-expr `(print (logxor 42 -1))))

;;; Shift operations (ash - arithmetic shift)
(deftest ash-left-basic (16)
  (el-expr `(print (ash 2 3))))

(deftest ash-right-basic (2)
  (el-expr `(print (ash 16 -3))))

(deftest ash-zero-shift (42)
  (el-expr `(print (ash 42 0))))

(deftest ash-zero-value (0)
  (el-expr `(print (ash 0 10))))

;;; Negative number shifts
(deftest ash-negative-left (-16)
  (el-expr `(print (ash -2 3))))

(deftest ash-negative-right (-1)
  (el-expr `(print (ash -2 -3))))

;;; Large shift amounts
(deftest ash-large-left (t)
  (el-expr `(let ((result (ash 1 100)))
              (print (and (integerp result) (> result 0))))))

(deftest ash-large-right (0)
  (el-expr `(print (ash 42 -100))))

;;; Operations at fixnum boundaries
(let ((mpf (greatest-fixnum))
      (mnf (least-fixnum)))

  ;; Logical operations at fixnum limits
  (deftestf 'logand-mpf-mpf (mpf)
    (el-expr `(let ((mpf most-positive-fixnum))
                (print (logand mpf mpf)))))

  (deftestf 'logior-mpf-zero (mpf)
    (el-expr `(let ((mpf most-positive-fixnum))
                (print (logior mpf 0)))))

  (deftestf 'logxor-mpf-zero (mpf)
    (el-expr `(let ((mpf most-positive-fixnum))
                (print (logxor mpf 0)))))

  (deftestf 'lognot-mpf ((lognot mpf))
    (el-expr `(let ((mpf most-positive-fixnum))
                (print (lognot mpf)))))

  (deftestf 'lognot-mnf ((lognot mnf))
    (el-expr `(let ((mnf most-negative-fixnum))
                (print (lognot mnf)))))

  ;; Shift operations at boundaries
  (deftestf 'ash-mpf-left-1 ((ash mpf 1))
    (el-expr `(let ((mpf most-positive-fixnum))
                (print (ash mpf 1)))))

  (deftestf 'ash-mpf-right-1 ((ash mpf -1))
    (el-expr `(let ((mpf most-positive-fixnum))
                (print (ash mpf -1)))))

  (deftestf 'ash-mnf-left-1 ((ash mnf 1))
    (el-expr `(let ((mnf most-negative-fixnum))
                (print (ash mnf 1)))))

  (deftestf 'ash-mnf-right-1 ((ash mnf -1))
    (el-expr `(let ((mnf most-negative-fixnum))
                (print (ash mnf -1))))))

;;; Bignum bitwise operations
(let ((big1 (expt 2 100))
      (big2 (expt 3 50)))

  (deftestf 'logand-bignums ((logand big1 big2))
    (el-expr `(print (logand ,big1 ,big2))))

  (deftestf 'logior-bignums ((logior big1 big2))
    (el-expr `(print (logior ,big1 ,big2))))

  (deftestf 'logxor-bignums ((logxor big1 big2))
    (el-expr `(print (logxor ,big1 ,big2))))

  (deftestf 'lognot-bignum ((lognot big1))
    (el-expr `(print (lognot ,big1)))))

;;; Bit counting operations
(deftest logcount-zero (0)
  (el-expr `(print (logcount 0))))

(deftest logcount-one (1)
  (el-expr `(print (logcount 1))))

(deftest logcount-all-ones (3)
  (el-expr `(print (logcount 7))))

'(deftest logcount-negative (-1)
  (el-expr `(print (logcount -1))))

(deftest logcount-power-of-two (1)
  (el-expr `(print (logcount 64))))

;;; Bit counting with large numbers
(let ((sparse-big (+ (expt 2 100) (expt 2 50) 1)))
  (deftestf 'logcount-sparse-big (3)
    (el-expr `(print (logcount ,sparse-big)))))

(let ((dense-big (- (expt 2 64) 1)))  ; all bits set in 64-bit range
  (deftestf 'logcount-dense-big (64)
    (el-expr `(print (logcount ,dense-big)))))

;;; Test patterns - alternating bits
(let ((alternating-1 #x55555555)  ; 01010101... pattern
      (alternating-2 #xAAAAAAAA)) ; 10101010... pattern

  (deftestf 'logand-alternating (0)
    (el-expr `(print (logand ,alternating-1 ,alternating-2))))

  (deftestf 'logior-alternating (#xFFFFFFFF)
    (el-expr `(print (logior ,alternating-1 ,alternating-2))))

  (deftestf 'logxor-alternating (#xFFFFFFFF)
    (el-expr `(print (logxor ,alternating-1 ,alternating-2)))))

;;; Power-of-2 operations
(for-each (lambda (power)
            (let ((pow2 (expt 2 power)))
              (deftestf (string->symbol (format #f "logcount-2pow~a" power)) (1)
                (el-expr `(print (logcount ,pow2))))

              (deftestf (string->symbol (format #f "lognot-2pow~a" power)) ((lognot pow2))
                (el-expr `(print (lognot ,pow2))))))
          '(0 1 2 3 4 5 10 16 20 30 31 32 60 61 62 63 64 100))

;;; Mask operations
(let ((mask-8bit #xFF)
      (mask-16bit #xFFFF)
      (mask-32bit #xFFFFFFFF))

  (deftestf 'mask-8bit-test (42)
    (el-expr `(print (logand 42 ,mask-8bit))))

  (deftestf 'mask-16bit-test (1234)
    (el-expr `(print (logand 1234 ,mask-16bit))))

  (let ((big-num (+ (expt 2 40) 12345)))
    (deftestf 'mask-32bit-big ((logand big-num mask-32bit))
      (el-expr `(print (logand ,big-num ,mask-32bit))))))

;;; Bit manipulation: set, clear, toggle specific bits
(let ((base-num 42))  ; Binary: 101010
  ;; Set bit 0 (LSB)
  (deftestf 'set-bit-0 ((logior base-num 1))
    (el-expr `(print (logior ,base-num 1))))

  ;; Clear bit 1
  (deftestf 'clear-bit-1 ((logand base-num (lognot 2)))
    (el-expr `(print (logand ,base-num ,(lognot 2)))))

  ;; Toggle bit 2
  (deftestf 'toggle-bit-2 ((logxor base-num 4))
    (el-expr `(print (logxor ,base-num 4)))))

;;; Shift patterns and edge cases
'(deftest ash-boundary-positive (t)
  (el-expr `(let ((result (ash 1 62)))
              (print (= result most-positive-fixnum)))))

'(deftest ash-overflow-to-bignum (t)
  (el-expr `(let ((result (ash 1 63)))
              (print (not (fixnump result))))))

;;; Combining operations
'(deftest combined-ops-1 (5)
  (el-expr `(print (logxor (logand 15 12) (logior 1 4)))))

(deftest combined-ops-2 (24)
  (el-expr `(print (ash (logior 1 2) 3))))

;;; Error conditions
'(deftest ash-non-integer-error (t)
  (el-expr `(condition-case err
                (progn (ash 3.5 2) nil)
              (wrong-type-argument t)
              (error t))))

'(deftest logand-non-integer-error (t)
  (el-expr `(condition-case err
                (progn (logand 5 3.14) nil)
              (wrong-type-argument t)
              (error t))))

;;; Associativity and commutativity tests
(deftest logand-associative (t)
  (el-expr `(let ((a 12) (b 8) (c 4))
              (print (= (logand (logand a b) c)
                        (logand a (logand b c)))))))

(deftest logior-associative (t)
  (el-expr `(let ((a 12) (b 8) (c 4))
              (print (= (logior (logior a b) c)
                        (logior a (logior b c)))))))

(deftest logand-commutative (t)
  (el-expr `(let ((a 12) (b 8))
              (print (= (logand a b) (logand b a))))))

(deftest logior-commutative (t)
  (el-expr `(let ((a 12) (b 8))
              (print (= (logior a b) (logior b a))))))

;;; De Morgan's laws
(deftest demorgan-law-1 (t)
  (el-expr `(let ((a 12) (b 8))
              (print (= (lognot (logand a b))
                        (logior (lognot a) (lognot b)))))))

(deftest demorgan-law-2 (t)
  (el-expr `(let ((a 12) (b 8))
              (print (= (lognot (logior a b))
                        (logand (lognot a) (lognot b)))))))

;;; Double negation
(deftest double-negation (t)
  (el-expr `(let ((a 42))
              (print (= a (lognot (lognot a)))))))

;;; Shift equivalences
(deftest ash-multiply-equivalence (t)
  (el-expr `(let ((n 7))
              (print (= (ash n 3) (* n 8))))))

(deftest ash-divide-equivalence (t)
  (el-expr `(let ((n 56))
              (print (= (ash n -3) (/ n 8))))))

;;; Large shift stress test
(deftest large-shift-stress (t)
  (el-expr `(let ((big-num (expt 2 200))
                  (shift-amt 50))
              (print (integerp (ash big-num shift-amt))))))
