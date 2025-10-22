; Floats produced with:
;
;     import GHC.Float
;     import Numeric
;     showString "0x" $ showHex (castDoubleToWord64 42.0) ""
;     showString "0x" $ showHex (castDoubleToWord64 (0.0 / 0.0)) ""

(defun @main () Unit
  (start start:
    (let g (resolve-global "isnan"))
    (let h (load-handle (Ptr 32) ((FP Double)) g))

    (let i42 (bv 64 0x4045000000000000))
    (let f42 (binary-to-fp Double i42))
    (let n (funcall h f42))
    (let n-off (ptr-offset 32 n))
    (assert! (equal? n-off (bv 32 0)) "42.0 is not NaN")

    (let iNaN (bv 64 0x7ff8000000000000))
    (let fNaN (binary-to-fp Double iNaN))
    (let y (funcall h fNaN))
    (let y-off (ptr-offset 32 y))
    (assert! (not (equal? y-off (bv 32 0))) "NaN is NaN")

    (return ())))
