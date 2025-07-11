; Regression test for #1466, wherein crucible-llvm-cli didn't register the
; intrinsic type for LLVM memory with the simulator, resulting in a panic.

(defun @main () Unit
  (start start:
    (let b (fresh Bool))
    (branch b if: end:))
  (defblock if:
    (jump end:))
  (defblock end:
    (return ())))
