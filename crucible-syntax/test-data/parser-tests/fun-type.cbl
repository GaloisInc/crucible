(defun @id ((x Bool)) Bool
  (start here: (return x)))

(defun @get-id () (-> Bool Bool)
  (start here:
    (let id @id)
    (return id)))
