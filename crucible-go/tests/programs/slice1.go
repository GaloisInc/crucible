package slice1

import "github.com/GaloisInc/crucible-go"

func main() {
	x, y := crucible.FreshInt32(), crucible.FreshInt32()
	
	crucible.Assume(x == 1, "", "")
	crucible.Assume(y == 2, "", "")
	
	slice := []int32{0, x, y}

	ptr := &slice[1]
	
	print(slice, ptr)
}
