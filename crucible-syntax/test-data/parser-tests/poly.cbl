(defpoly ('A) @id ((x 'A)) 'A
  (start here:
    (return x)))

(defun @bool-id () (-> Bool Bool)
   (start here:
     (let id @id)
     (let bool-id (inst id Bool))
     (return bool-id)))
