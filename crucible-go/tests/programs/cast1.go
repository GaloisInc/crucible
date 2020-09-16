package cast1

// Testing of preliminary type conversion (not finished / correct).

import "github.com/GaloisInc/go-crucible"

func main() {
	var x int32 = 123
	var y int64 = int64(x)

	var z int = int(x) + int(y) + 5

	crucible.Assert(z == 251, " ", " ")
}
