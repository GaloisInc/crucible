package slice2

import "github.com/GaloisInc/go-crucible"

// func f(x int32, xs ...int32) int32 {
// 	// return x + xs[0]
// 	return x
// }

func f(xs ...int32) int32 {
	return xs[0] + xs[1]
	// return 0
}

func g(x int32, xs ...int32) int32 {
	return x + xs[0] + xs[1]
}

func main() {
	x, y := crucible.FreshInt32(), crucible.FreshInt32()
	crucible.Assume(x == 1, "", "")
	crucible.Assume(y == 2, "", "")

	z := f(11, 4)
	crucible.Assert(z == 15, "", "")

	z = f([]int32{z, 5}...)
	crucible.Assert(z == 20, "", "")

	slice := []int32{x, y}
	z = f(slice...)
	crucible.Assert(z == x + y, "", "")

	z = g(z, 2, 3)
	crucible.Assert(z == x + y + 2 + 3, "", "")
}
