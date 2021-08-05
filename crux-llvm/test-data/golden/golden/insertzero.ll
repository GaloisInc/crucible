define internal { i64*, i64 } @insertzero(i64*) {
  %2 = getelementptr inbounds i64, i64* %0, i64 0
  %3 = insertvalue { i64*, i64 } undef, i64* %2, 0
  %4 = insertvalue { i64*, i64 } %3, i64 0, 1
  ret { i64*, i64 } %4
}

define i64 @main () {
  %x = alloca [16 x i8], align 16
  %y = bitcast [16 x i8]* %x to i64*
  %z = call { i64*, i64 } @insertzero(i64* %y)
  %v = extractvalue { i64*, i64 } %z, 1
  ret i64 %v
}