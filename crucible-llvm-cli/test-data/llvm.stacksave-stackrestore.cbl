(declare @llvm.stacksave.p0 () Pointer)
(declare @llvm.stackrestore.p0 ((x Pointer)) Unit)

(defun @main () Unit
  (start start:
    (let ptr (funcall @llvm.stacksave.p0))
    (funcall @llvm.stackrestore.p0 ptr)
    (return ())))
