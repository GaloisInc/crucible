package for3

import "github.com/GaloisInc/go-crucible"

func main() {
	count := 0
Outer:
	for i := 0; i < 2; i++ {
		for j := 0; j < 3; j++ {
			if j == 1 {
				//continue
				continue Outer
			}
			count++
		}
	}
	// If the Outer label is omitted from the continue statement,
	// count ends up equal to 4 instead.
	crucible.Assert(count == 2, "", "")
}
