define internal [3 x i64] @insertzero(i64 %a, i64 %b) {
  %a1 = insertvalue [3 x i64] undef, i64 %a, 0
  %a2 = insertvalue [3 x i64] %a1, i64 %b, 1
  %a3 = insertvalue [3 x i64] %a2, i64 0, 2
  ret [3 x i64] %a3
}

define i64 @main () {
  %z = call [3 x i64] @insertzero(i64 42, i64 1234)
  %v = extractvalue [3 x i64] %z, 1
  ret i64 %v
}