package array_bounds

import "github.com/GaloisInc/crucible-go"

func f(xs []int) int {
	return xs[1]
}

func g(i int) int {
	arr := [3]int{0, 1, 2}
	return arr[i]
}

func main() {
	arr := [3]int{3, 123, 5}
	crucible.Assert(f(arr[:]) == 123, "", "")

	// This should throw an out-of-bounds error.
	// slice := []int{2}
	// print(slice[1])

	// This should too.
	// print(g(5))
}
