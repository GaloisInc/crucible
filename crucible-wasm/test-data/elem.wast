;; Test the element section
;;
;; Adapted from the elem test case in
;;
;;   https://github.com/WebAssembly/spec/blob/351d8b1026a2a820e88baae54557c43e775fd5a5/test/core/elem.wast

;; Syntax
(module
  (table $t 10 funcref)
  (func $f)
  (func $g)

  ;; Active
  (elem (table $t) (i32.const 0) funcref)
  (elem (table $t) (i32.const 0) funcref (ref.func $f) (ref.func $g))
  (elem (table $t) (i32.const 0) func)
  (elem (table $t) (i32.const 0) func $f $g)
  (elem (table $t) (offset (i32.const 0)) funcref)
  (elem (table $t) (offset (i32.const 0)) func $f $g)
  (elem (table 0) (i32.const 0) func)
  (elem (table 0x0) (i32.const 0) func $f $f)
  (elem (table 0x000) (offset (i32.const 0)) func)
  (elem (table 0) (offset (i32.const 0)) func $f $f)
  (elem (table $t) (i32.const 0) func)
  (elem (table $t) (i32.const 0) func $f $f)
  (elem (table $t) (offset (i32.const 0)) func)
  (elem (table $t) (offset (i32.const 0)) func $f $f)
  (elem (offset (i32.const 0)))
  (elem (offset (i32.const 0)) funcref (ref.func $f) (ref.func $g))
  (elem (offset (i32.const 0)) func $f $f)
  (elem (offset (i32.const 0)) $f $f)
  (elem (i32.const 0))
  (elem (i32.const 0) funcref (ref.func $f) (ref.func $g))
  (elem (i32.const 0) func $f $f)
  (elem (i32.const 0) $f $f)
  (elem (i32.const 0) funcref (item (ref.func $f)) (item (ref.func $g)))

  (elem $a1 (table $t) (i32.const 0) funcref)
  (elem $a2 (table $t) (i32.const 0) funcref (ref.func $f) (ref.func $g))
  (elem $a3 (table $t) (i32.const 0) func)
  (elem $a4 (table $t) (i32.const 0) func $f $g)
  (elem $a9 (table $t) (offset (i32.const 0)) funcref)
  (elem $a10 (table $t) (offset (i32.const 0)) func $f $g)
  (elem $a11 (table 0) (i32.const 0) func)
  (elem $a12 (table 0x0) (i32.const 0) func $f $f)
  (elem $a13 (table 0x000) (offset (i32.const 0)) func)
  (elem $a14 (table 0) (offset (i32.const 0)) func $f $f)
  (elem $a15 (table $t) (i32.const 0) func)
  (elem $a16 (table $t) (i32.const 0) func $f $f)
  (elem $a17 (table $t) (offset (i32.const 0)) func)
  (elem $a18 (table $t) (offset (i32.const 0)) func $f $f)
  (elem $a19 (offset (i32.const 0)))
  (elem $a20 (offset (i32.const 0)) funcref (ref.func $f) (ref.func $g))
  (elem $a21 (offset (i32.const 0)) func $f $f)
  (elem $a22 (offset (i32.const 0)) $f $f)
  (elem $a23 (i32.const 0))
  (elem $a24 (i32.const 0) funcref (ref.func $f) (ref.func $g))
  (elem $a25 (i32.const 0) func $f $f)
  (elem $a26 (i32.const 0) $f $f)
)

(module
  (func $f)
  (func $g)

  (table $t funcref (elem (ref.func $f) (ref.func $g) (ref.func $g)))
)


;; Basic use

(module
  (table 10 funcref)
  (func $f)
  (elem (i32.const 0) $f)
)

(module
  (table 10 funcref)
  (func $f)
  (elem (i32.const 0) $f)
  (elem (i32.const 3) $f)
  (elem (i32.const 7) $f)
  (elem (i32.const 5) $f)
  (elem (i32.const 3) $f)
)

(module
  (type $out-i32 (func (result i32)))
  (table 10 funcref)
  (elem (i32.const 7) $const-i32-a)
  (elem (i32.const 9) $const-i32-b)
  (func $const-i32-a (type $out-i32) (i32.const 65))
  (func $const-i32-b (type $out-i32) (i32.const 66))
  (func (export "call-7") (type $out-i32)
    (call_indirect (type $out-i32) (i32.const 7))
  )
  (func (export "call-9") (type $out-i32)
    (call_indirect (type $out-i32) (i32.const 9))
  )
)
(assert_return (invoke "call-7") (i32.const 65))
(assert_return (invoke "call-9") (i32.const 66))

;; Corner cases

(module
  (table 10 funcref)
  (func $f)
  (elem (i32.const 9) $f)
)

(module
  (table 0 funcref)
  (elem (i32.const 0))
)

(module
  (table 0 0 funcref)
  (elem (i32.const 0))
)

(module
  (table 20 funcref)
  (elem (i32.const 20))
)

;; Two elements target the same slot

(module
  (type $out-i32 (func (result i32)))
  (table 10 funcref)
  (elem (i32.const 9) $const-i32-a)
  (elem (i32.const 9) $const-i32-b)
  (func $const-i32-a (type $out-i32) (i32.const 65))
  (func $const-i32-b (type $out-i32) (i32.const 66))
  (func (export "call-overwritten") (type $out-i32)
    (call_indirect (type $out-i32) (i32.const 9))
  )
)
(assert_return (invoke "call-overwritten") (i32.const 66))
