package function1

import "github.com/GaloisInc/go-crucible"

func f(x int64, y float64, z ...string) int64 {
	return x
}

func g(x int64, y float64, z ...string) float64 {
	return y
}

func h(x int64, y float64, z ...string) string {
	return z[0]
}

func main() {
	x, y, z := crucible.FreshInt64(), crucible.FreshFloat64(), crucible.FreshString()
	crucible.Assert(f(x, y, z) == x, "", "")
	crucible.Assert(g(x, y) == y, "", "")
	crucible.Assert(h(x, y, z) == z, "", "")
	crucible.Assert(h(x, y, z, "another string") == z, "", "")
	crucible.Assert(h(x, y, z, "another string") != "another string", "", "")
}
