package ptr1

import "github.com/GaloisInc/go-crucible"

func main() {
	var x int = crucible.FreshInt()
	var y *int = &x

	crucible.Assume(x == 1, "", "")

	*y++

	crucible.Assert(x == 2, "", "")

	z := *y * 3

	crucible.Assert(z == 6, "", "")

	ptr := new(int)
	*ptr = 5
	crucible.Assert(*ptr * z == 30, "", "")
	
	print(x, y)
}
