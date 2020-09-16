package tuple2

import "github.com/GaloisInc/go-crucible"

func f(x int, y float32, z string) (int, float32, string) {
	return x, y, z
}

func g() (x int, y float32, z string) {
	x, y, z = 123, 5.43, "ggg"
	return
}

func main() {
	// threading a tuple return value through a call to f
	x, y, z := f(g())
	crucible.Assert(x == 123 && y == 5.43 && z == "ggg", "", "")
}
