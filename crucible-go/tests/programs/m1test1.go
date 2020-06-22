package m1test1

func f (x int32) int32 {
	var w int32 = 2 + x;
	return w
}

func g (z int32, y bool, w string) int32 {
	if y {
		return z
	} else { 
		return 0
	}
}

func h(k func(int32)(int32)) int32 {
	return k(0)
}

// func main () {
// 	var x int32 = 0;
// 	var y = f(x)
// }

// func test () {
// 	return
// }


func main () {
	// var x int32 = 123;
	// var y int32 = f(123);
	// var f = nil;
	// var y int32 = g(123, true, "hello");
	var x int32 = h(nil);
        return
}


// func test () {
// 	return
// }
