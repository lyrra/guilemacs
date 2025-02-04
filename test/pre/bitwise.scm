
(for-each (lambda (n)
            (let ((c (logcount n)))
              (deftestf 'logcount (c)
                (el-expr `(let ((n ,n))
                            (print (logcount n)))))))
          `(0
            1
            -1
            ,(random (ash 1 64))
            ,(random (ash 1 128))
            ,(random (ash 1 256))
            ,(- (random (ash 1 64)))))

(for-each (lambda (n)
            (let ((c (ash 1 n)))
              (deftestf 'ash (c)
                (el-expr `(let ((n ,n))
                            (print (ash 1 n))))))
            (let ((c (ash n 2)))
              (deftestf 'ash (c)
                (el-expr `(let ((n ,n))
                            (print (ash n 2)))))))
          `(0
            1
            -1
            ,(random 64)
            ,(- (random 64))
            ,(+ (random 128) 64)
            ,(- (- (random 128)) 64)))

(for-each (lambda (n)
            (let ((c (lognot n)))
              (deftestf 'lognot (c)
                (el-expr `(let ((n ,n))
                            (print (lognot n)))))))
          `(0
            1
            -1
            ,(random 64)
            ,(- (random 64))
            ,(+ (random 128) 64)
            ,(- (- (random 128)) 64)))

(for-each (lambda (n)
            (let ((c (logxor n)))
              (deftestf 'logxor (c)
                (el-expr `(let ((n ,n))
                            (print (logxor n)))))))
          `(0
            1
            -1
            ,(random 64)
            ,(- (random 64))
            ,(+ (random 128) 64)
            ,(- (- (random 128)) 64)))

(for-each (lambda (n)
            (let ((c (logior n)))
              (deftestf 'logior (c)
                (el-expr `(let ((n ,n))
                            (print (logior n)))))))
          `(0
            1
            -1
            ,(random 64)
            ,(- (random 64))
            ,(+ (random 128) 64)
            ,(- (- (random 128)) 64)))
