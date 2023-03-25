;; Adapted from the break-multi-value test cases in
;;
;;   https://github.com/WebAssembly/spec/blob/f60370c6f15546811e8603df71e7432ddf3dab49/test/core/if.wast
;;
;; and
;;
;;   https://github.com/WebAssembly/spec/blob/f60370c6f15546811e8603df71e7432ddf3dab49/test/core/loop.wast

(module
  (func (export "if-break-multi-value") (param i32) (result i32 i32 i64)
    (if (result i32 i32 i64) (local.get 0)
      (then
        (br 0 (i32.const 18) (i32.const -18) (i64.const 18))
        (i32.const 19) (i32.const -19) (i64.const 19)
      )
      (else
        (br 0 (i32.const -18) (i32.const 18) (i64.const -18))
        (i32.const -19) (i32.const 19) (i64.const -19)
      )
    )
  )
  (func (export "loop-break-multi-value") (result i32 i32 i64)
    (block (result i32 i32 i64)
      (i32.const 0) (i32.const 0) (i64.const 0)
      (loop (param i32 i32 i64)
        (block (br 2 (i32.const 18) (i32.const -18) (i64.const 18)))
        (br 0 (i32.const 20) (i32.const -20) (i64.const 20))
      )
      (i32.const 19) (i32.const -19) (i64.const 19)
    )
  )
)

(assert_return (invoke "if-break-multi-value" (i32.const 0))
  (i32.const -18) (i32.const 18) (i64.const -18)
)
(assert_return (invoke "loop-break-multi-value")
  (i32.const 18) (i32.const -18) (i64.const 18)
)
