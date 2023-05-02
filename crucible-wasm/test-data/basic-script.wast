(module
  (func (export "main") (result i32)
    i32.const 42
    return))

(assert_return (invoke "main") (i32.const 42))
