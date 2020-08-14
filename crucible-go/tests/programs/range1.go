package range1

import "github.com/GaloisInc/go-crucible"

func main() {
	xs := make([]int, 3)
	// xs := []int{1, 0, 5}

	xs[0] = 1
	xs[2] = 3

	sum := 0
	
	for i, x := range xs {
		sum += i + x
		print(sum, " ")
	}
	crucible.Assert(sum == 7, "", "")

	for i := range xs {
		sum += i
	}
	crucible.Assert(sum == 10, "", "")

	for i, _ := range xs {
		sum += i
	}
	crucible.Assert(sum == 13, "", "")

	for _, x := range xs {
		sum += x
	}
	crucible.Assert(sum == 17, "", "")
}
