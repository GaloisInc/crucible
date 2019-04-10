;; exercise floating-point expression formers

(defun @test-float () Unit
  (start start:
    (let a_f (fresh (FP Float)))
    (let b_d (fresh (FP Double)))
    (let c_h (fresh (FP Half)))
    (let d_q (fresh (FP Quad)))
    (let e_dd (fresh (FP DoubleDouble)))
    (let f_x87 (fresh (FP X86_80)))

    (let r1 (fresh Real))
    (let r2 (fresh Real))
    (let r3 (fresh Real))

    (let bv16 (fresh (Bitvector 16)))
    (let bv32 (fresh (Bitvector 32)))
    (let bv64 (fresh (Bitvector 64)))
    (let bv128 (fresh (Bitvector 128)))
    (let bv80 (fresh (Bitvector 80)))

    (let f16 (binary-to-fp Half bv16))
    (let f32 (binary-to-fp Float bv32))
    (let f64 (binary-to-fp Double bv64))
    (let f128 (binary-to-fp Quad bv128))
    (let fdd (binary-to-fp DoubleDouble bv128))
    (let f80 (binary-to-fp X86_80 bv80))

    (let n1 (fp-to-binary a_f))
    (let n2 (fp-to-binary b_d))
    (let n3 (fp-to-binary c_h))
    (let n4 (fp-to-binary d_q))
    (let n5 (fp-to-binary e_dd))
    (let n6 (fp-to-binary f_x87))

    (let u1 (ubv-to-fp Half rne bv64))
    (let u2 (ubv-to-fp Float rna bv16))
    (let u3 (ubv-to-fp Double rtp bv32))
    (let u4 (ubv-to-fp Quad rtn bv80))
    (let u5 (ubv-to-fp DoubleDouble rtz bv64))

    (let s1 (sbv-to-fp Half rne bv64))
    (let s2 (sbv-to-fp Float rna bv16))
    (let s3 (sbv-to-fp Double rtp bv32))
    (let s4 (sbv-to-fp Quad rtn bv80))
    (let s5 (sbv-to-fp DoubleDouble rtz bv64))

    (let x1 (fp-to-ubv 32 rne a_f))
    (let x2 (fp-to-ubv 40 rna b_d))
    (let x3 (fp-to-ubv 64 rtp c_h))
    (let x4 (fp-to-ubv 16 rtn d_q))
    (let x5 (fp-to-ubv 128 rtz e_dd))

    (let y1 (fp-to-sbv 32 rne a_f))
    (let y2 (fp-to-sbv 40 rna b_d))
    (let y3 (fp-to-sbv 64 rtp c_h))
    (let y4 (fp-to-sbv 16 rtn d_q))
    (let y5 (fp-to-sbv 128 rtz e_dd))

    (let w1 (fp-to-real a_f))
    (let w2 (fp-to-real b_d))
    (let w3 (fp-to-real c_h))
    (let w4 (fp-to-real d_q))
    (let w5 (fp-to-real e_dd))
    (let w6 (fp-to-real f_x87))

    (let q1 (real-to-fp Float rne r1))
    (let q2 (real-to-fp Double rna r2))
    (let q3 (real-to-fp Half rtp r3))
    (let q4 (real-to-fp DoubleDouble rtn r1))
    (let q5 (real-to-fp X86_80 rtz r2))

    (let b (fresh Bool))
    (let ite (if b u3 q2))

    (return ()))
)
