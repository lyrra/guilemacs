(princ "\n-- test begin: value-lt (0 1)\n")
(princ (value< 0 1))
(princ "\n-- test expect: t\n")
(princ "-- test end: value-lt (0 1)\n")


(princ "\n-- test begin: value-lt (1 0)\n")
(princ (value< 1 0))
(princ "\n-- test expect: nil\n")
(princ "-- test end: value-lt (1 0)\n")


(princ "\n-- test begin: value-lt (1 1)\n")
(princ (value< 1 1))
(princ "\n-- test expect: nil\n")
(princ "-- test end: value-lt (1 1)\n")


(princ "\n-- test begin: value-lt (0.0 1.0)\n")
(princ (value< 0.0 1.0))
(princ "\n-- test expect: t\n")
(princ "-- test end: value-lt (0.0 1.0)\n")


(princ "\n-- test begin: value-lt (1.0 0.0)\n")
(princ (value< 1.0 0.0))
(princ "\n-- test expect: nil\n")
(princ "-- test end: value-lt (1.0 0.0)\n")


(princ "\n-- test begin: value-lt (1.0 1.0)\n")
(princ (value< 1.0 1.0))
(princ "\n-- test expect: nil\n")
(princ "-- test end: value-lt (1.0 1.0)\n")
