package for1

import "github.com/GaloisInc/go-crucible"

func main() {
	x, y, z := crucible.FreshInt(), crucible.FreshInt(), crucible.FreshInt()
	slice := []int{x, y, z}
	sum := 0
	for i := 0; i < len(slice); i++ {
		sum += slice[i]
	}
	crucible.Assert(sum == x+y+z, "", "")
}
