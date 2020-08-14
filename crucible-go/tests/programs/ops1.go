package ops1

import "github.com/GaloisInc/crucible-go"

func main() {
	x := (1 + 2.5) * 3.2 / 1.9
	crucible.Assert(5.89 < x && x < 5.9, "", "")

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
}

// data BinaryOp =
//   BPlus -- ^ +
//   | BMinus -- ^ -
//   | BMult -- ^ *
//   | BDiv -- ^ /
//   | BMod -- ^ %
//   | BAnd -- ^ &
//   | BOr -- ^ |
//   | BXor -- ^ ^
//   | BShiftL -- ^ <<
//   | BShiftR -- ^ >>
//   | BAndNot -- ^ &^
//   | BLAnd -- ^ logical AND
//   | BLOr -- ^ logical OR
//   | BEq -- ^ ==
//   | BLt -- ^ <
//   | BGt -- ^ >
//   | BNeq -- ^ !=
//   | BLeq -- ^ <=
//   | BGeq -- ^ >=
//   deriving (Eq, Show)
