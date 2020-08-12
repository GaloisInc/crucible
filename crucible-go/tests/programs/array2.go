package array1

import "github.com/GaloisInc/crucible-go"

func main() {
	x, y := crucible.FreshInt32(), crucible.FreshInt32()
	
	crucible.Assume(x == 1, "", "")
	crucible.Assume(y == 2, "", "")
	
	arr := [5]int32{0, x, y, 3, 4}

	z := len(arr) + 1
	crucible.Assert(z == 6, "", "")
}
