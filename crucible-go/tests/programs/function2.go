package function2

import "github.com/GaloisInc/go-crucible"

func f(x int64, y float64, z ...string) (a float64, b int64, c string) {
	a = y
	b = x
	c = z[0]
	return
}

func main() {
	x, y, z := crucible.FreshInt64(), crucible.FreshFloat64(), crucible.FreshString()
	a, b, c := f(x, y, z, "another string")
	crucible.Assert(a == y, "", "")
	crucible.Assert(b == x, "", "")
	crucible.Assert(c == z, "", "")
	print(x, y, z, a, b, c)
}
