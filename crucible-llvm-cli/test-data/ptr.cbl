(defun @main () Unit
  (start start:
    (let blk0 (the Nat 0))
    (let off0 (bv 64 0))
    (let p0 (ptr 64 blk0 off0))
    (let p (ptr-ite 64 #t p0 p0))
    (let blk (ptr-block 64 p))
    (let off (ptr-offset 64 p))
    (assert! (equal? blk0 blk) "block numbers equal")
    (assert! (equal? off0 off) "offsets equal")

    (let sz (bv 64 1))
    (let a (alloca none sz))
    (let vblk0 (the Nat 0))
    (let voff0 (bv 8 255))
    (let v0 (ptr 8 vblk0 voff0))
    (store none i8 a v0)
    (let v (load none i8 a))
    (let vblk (ptr-block 8 v))
    (let voff (ptr-offset 8 v))
    (assert! (equal? vblk0 vblk) "stored block numbers equal")
    (assert! (equal? voff0 voff) "stored offsets equal")

    (let g (resolve-global "malloc"))
    (let gblk (ptr-block 64 g))
    (assert! (not (equal? gblk 0)) "malloc block number nonzero")
    (let h (load-handle (Ptr 64) ((Ptr 64)) g))
    (let m (funcall h p0))
    (let mblk (ptr-block 64 m))
    (assert! (not (equal? mblk 0)) "malloc'd block number nonzero")

    (return ())))