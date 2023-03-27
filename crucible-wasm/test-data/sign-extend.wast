;; Adapted from the WebAssembly reference interpreter's test cases in
;;
;;   https://github.com/WebAssembly/spec/blob/f60370c6f15546811e8603df71e7432ddf3dab49/test/core/i32.wast
;;
;; and
;;
;;   https://github.com/WebAssembly/spec/blob/f60370c6f15546811e8603df71e7432ddf3dab49/test/core/i64.wast
(module
  (func (export "i32.extend8_s") (param $x i32) (result i32) (i32.extend8_s (local.get $x)))
  (func (export "i32.extend16_s") (param $x i32) (result i32) (i32.extend16_s (local.get $x)))
  (func (export "i64.extend8_s") (param $x i64) (result i64) (i64.extend8_s (local.get $x)))
  (func (export "i64.extend16_s") (param $x i64) (result i64) (i64.extend16_s (local.get $x)))
  (func (export "i64.extend32_s") (param $x i64) (result i64) (i64.extend32_s (local.get $x)))
)

(assert_return (invoke "i32.extend8_s" (i32.const 0)) (i32.const 0))
(assert_return (invoke "i32.extend8_s" (i32.const 0x7f)) (i32.const 127))
(assert_return (invoke "i32.extend8_s" (i32.const 0x80)) (i32.const -128))
(assert_return (invoke "i32.extend8_s" (i32.const 0xff)) (i32.const -1))
(assert_return (invoke "i32.extend8_s" (i32.const 0x012345_00)) (i32.const 0))
(assert_return (invoke "i32.extend8_s" (i32.const 0xfedcba_80)) (i32.const -0x80))
(assert_return (invoke "i32.extend8_s" (i32.const -1)) (i32.const -1))

(assert_return (invoke "i32.extend16_s" (i32.const 0)) (i32.const 0))
(assert_return (invoke "i32.extend16_s" (i32.const 0x7fff)) (i32.const 32767))
(assert_return (invoke "i32.extend16_s" (i32.const 0x8000)) (i32.const -32768))
(assert_return (invoke "i32.extend16_s" (i32.const 0xffff)) (i32.const -1))
(assert_return (invoke "i32.extend16_s" (i32.const 0x0123_0000)) (i32.const 0))
(assert_return (invoke "i32.extend16_s" (i32.const 0xfedc_8000)) (i32.const -0x8000))
(assert_return (invoke "i32.extend16_s" (i32.const -1)) (i32.const -1))

(assert_return (invoke "i64.extend8_s" (i64.const 0)) (i64.const 0))
(assert_return (invoke "i64.extend8_s" (i64.const 0x7f)) (i64.const 127))
(assert_return (invoke "i64.extend8_s" (i64.const 0x80)) (i64.const -128))
(assert_return (invoke "i64.extend8_s" (i64.const 0xff)) (i64.const -1))
(assert_return (invoke "i64.extend8_s" (i64.const 0x01234567_89abcd_00)) (i64.const 0))
(assert_return (invoke "i64.extend8_s" (i64.const 0xfedcba98_765432_80)) (i64.const -0x80))
(assert_return (invoke "i64.extend8_s" (i64.const -1)) (i64.const -1))

(assert_return (invoke "i64.extend16_s" (i64.const 0)) (i64.const 0))
(assert_return (invoke "i64.extend16_s" (i64.const 0x7fff)) (i64.const 32767))
(assert_return (invoke "i64.extend16_s" (i64.const 0x8000)) (i64.const -32768))
(assert_return (invoke "i64.extend16_s" (i64.const 0xffff)) (i64.const -1))
(assert_return (invoke "i64.extend16_s" (i64.const 0x12345678_9abc_0000)) (i64.const 0))
(assert_return (invoke "i64.extend16_s" (i64.const 0xfedcba98_7654_8000)) (i64.const -0x8000))
(assert_return (invoke "i64.extend16_s" (i64.const -1)) (i64.const -1))

(assert_return (invoke "i64.extend32_s" (i64.const 0)) (i64.const 0))
(assert_return (invoke "i64.extend32_s" (i64.const 0x7fff)) (i64.const 32767))
(assert_return (invoke "i64.extend32_s" (i64.const 0x8000)) (i64.const 32768))
(assert_return (invoke "i64.extend32_s" (i64.const 0xffff)) (i64.const 65535))
(assert_return (invoke "i64.extend32_s" (i64.const 0x7fffffff)) (i64.const 0x7fffffff))
(assert_return (invoke "i64.extend32_s" (i64.const 0x80000000)) (i64.const -0x80000000))
(assert_return (invoke "i64.extend32_s" (i64.const 0xffffffff)) (i64.const -1))
(assert_return (invoke "i64.extend32_s" (i64.const 0x01234567_00000000)) (i64.const 0))
(assert_return (invoke "i64.extend32_s" (i64.const 0xfedcba98_80000000)) (i64.const -0x80000000))
(assert_return (invoke "i64.extend32_s" (i64.const -1)) (i64.const -1))
