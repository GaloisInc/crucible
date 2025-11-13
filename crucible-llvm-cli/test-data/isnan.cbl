; Floats produced with:
;
;     import GHC.Float
;     import Numeric
;     showString "0x" $ showHex (castDoubleToWord64 42.0) ""
;     showString "0x" $ showHex (castDoubleToWord64 (0.0 / 0.0)) ""

(declare @isnan ((f (FP Double))) (Bitvector 32))

(defun @main () Unit
  (start start:
    (let i42 (bv 64 0x4045000000000000))
    (let f42 (binary-to-fp Double i42))
    (let n (funcall @isnan f42))
    (assert! (equal? n (bv 32 0)) "42.0 is not NaN")

    (let iNaN (bv 64 0x7ff8000000000000))
    (let fNaN (binary-to-fp Double iNaN))
    (let y (funcall @isnan fNaN))
    (assert! (not (equal? y (bv 32 0))) "NaN is NaN")

    (return ())))
