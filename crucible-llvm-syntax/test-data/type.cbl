(defun @test-type () Unit
  (start start:
    (let byte (the Byte (bv 8 0)))
    (let int (the Int (bv 32 0)))
    (let long (the Long (bv 64 0)))
    (let pid (the PidT (bv 32 0)))
    (let blk (the Nat 0))
    (let off (bv 64 0))
	(let p (ptr 64 blk off))
    (let ptr (the Pointer p))
    (let short (the Short (bv 16 0)))
    (let size (the SizeT (bv 64 0)))
    (return ())))
