package ops1

// Testing binary and unary operations.

import "github.com/GaloisInc/crucible-go"

func main() {
	x := (1 + 2.5) * 3.2 / 1.9 - 1.5 + (-1.0)
	crucible.Assert(x > 3.39 && x < 3.4, "", "")

	y := 3 * 57 / 2 % 3
	crucible.Assert(y == 1, "", "")

	// This RHS is constant-evaluated.
	z := 1 << 0 | 1 << 1 | 1 << 2
	crucible.Assert(z == 7, "", "")

	// Here the translator must actually implement the shift.
	z = z & 1 << 1
	crucible.Assert(z == 2, "", "")

	z = z << 3 >> 2
	crucible.Assert(z == 4, "", "")
	crucible.Assert(! (z != 4), "", "")

	z = z &^ 0
	crucible.Assert(z == 4, "", "")

	z = z &^ (^0)
	crucible.Assert(z == 0, "", "")

	z |= 1 << 5
	crucible.Assert(z == 32, "", "")

	z ^= +25
	crucible.Assert(z == 57, "", "")

	crucible.Assert(!(z != z) && true || false && !false, "", "")

	// Prove antisymmetry of <= on int.
	a, b := crucible.FreshInt(), crucible.FreshInt()
	crucible.Assume(a <= b && a >= b, "", "")
	crucible.Assert(a == b, "", "")
}
