package array1

import "github.com/GaloisInc/go-crucible"

func main() {
	x, y := crucible.FreshInt32(), crucible.FreshInt32()
	
	crucible.Assume(x == 1 && y == 2, "", "")
	
	arr := [5]int32{0, x, y, 3, 4}

	ptr := &arr[1]
	*ptr += 2

	crucible.Assert(*ptr == 3, "", "")
	crucible.Assert(arr[1] == 3, "", "")

	*ptr *= 5
	crucible.Assert(arr[1] == 3*5, "", "")

	var z = *ptr
	z /= 2
	crucible.Assert(z == *ptr / 2, "", "")
	crucible.Assert(arr[1] == 3*5, "", "")

	arr[1]++
	crucible.Assert(*ptr == 3*5+1, "", "")

	ptr2 := ptr
	ptr = &arr[2]
	crucible.Assert(*ptr == y, "", "")
	crucible.Assert(*ptr2 == 3*5+1, "", "")
	
	print(arr, ptr)
}
