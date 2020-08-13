package globals1

import "github.com/GaloisInc/go-crucible"

var w = z / 3
const y = x + 1
var z = y * 2
const x = 123

func main() {
	crucible.Assert(x == 123, "", "")
	crucible.Assert(y == 124, "", "")
	crucible.Assert(z == 248, "", "")
	crucible.Assert(w == 82, "", "")
}
