; Test the prove-online override which uses onlineProve
; to check proof obligations and return a Bool
; Note: there may be bugs in onlineProve

(defun @main () Unit
  (start start:
    ; Test 1: Create a simple provable assertion: x == 5 -> x > 0
    (let x (fresh Integer))
    (assume! (equal? x 5) "x equals 5")
    (assert! (< 0 x) "x is positive")

    ; Call prove-online, which should return true
    (let result1 (funcall @prove-online))
    (println (show result1))

    ; Test 2: Create a failing assertion: y == 5 -> y < 0
    (let y (fresh Integer))
    (assume! (equal? y 5) "y equals 5")
    (assert! (< y 0) "y is negative (should fail)")

    ; Call prove-online, which should return false
    (let result2 (funcall @prove-online))
    (println (show result2))

    (return ())))
