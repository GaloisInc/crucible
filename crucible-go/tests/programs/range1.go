package range1

import "github.com/GaloisInc/go-crucible"

func main() {
	xs := make([]int, 3)
	xs[0] = 1
	xs[2] = 3

	sum := 0
	for i, x := range xs {
		sum += i + x
	}
	crucible.Assert(sum == 7, "", "")
}
