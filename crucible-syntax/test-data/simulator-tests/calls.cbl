(defun @main () Unit
  (start start:
    (let x (fresh Integer))
    (let y (funcall @f x))
    (let z (funcall @nosuchfn))
    (println (show x))
    (println (show y))
    (assert! (equal? x y) "bogus")
    (return ())))

(defun @f ((x Integer)) Integer
  (start start:
    (let x10 (+ x 10))
    (let y (funcall @g x10))
    (tail-call @h y)))

(defun @g ((x Integer)) Integer
  (start start:
    (return (+ x 12))))

(defun @h ((x Integer)) Integer
  (start start:
    (return (+ x 20))))
