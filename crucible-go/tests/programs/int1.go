package int1

import "github.com/GaloisInc/crucible-go"

func main() {
	var x int32 = crucible.FreshInt32()
	var y int32 = crucible.FreshInt32()
	var z int32 = 5

	// Leaving out one of these assumptions causes the final
	// assertion to fail.
	crucible.Assume(0 <= x && x <= 100, "", "")
	crucible.Assume(0 <= y && y <= 50, "", "")

	// These assertions fail.
	// crucible.Assert(x + y + z <= 154, "", "")
	// crucible.Assert(x + y - z < 145, "", "")

	// These succeed.
	crucible.Assert(x + y + z <= 155, "", "")
	crucible.Assert(x + y - z < 146, "", "")

	print(x, y, z)
}
