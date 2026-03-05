;; exercise string literals and operations

(defun @test-str () (String Unicode)
  (start start:
    (let x "a")
    (let y "\\")
    (let q "\"")
    (let w "\t\n ")
    (let e (string-empty Unicode))
    (let c (string-concat x y))
    (let n (string-length x))
    (return x)))
