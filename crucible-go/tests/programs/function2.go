package function2

import "github.com/GaloisInc/go-crucible"

// Test variadic argument and named return values.
func f(x int64, y float64, z ...string) (a float64, b int64, c string) {
	a = y
	b = x
	c = z[0]
	return
	// Naked return is equivalent to:
	// return a, b, c
}

func g() (x int, y int) {
	x = 1
	y = 2
	// Note that this is allowed for some reason (the order of
	// return values can be rearranged as long as the types match
	// up).
	return y, x
}

func main() {
	x, y := crucible.FreshInt64(), crucible.FreshFloat64()
	zs := []string{"hello", "another string"}
	a, b, c := f(x, y, zs...)
	crucible.Assert(a == y, "", "")
	crucible.Assert(b == x, "", "")
	crucible.Assert(c == "hello", "", "")
	print(x, y, a, b, c)

	i, j := g()
	crucible.Assert(i == 2 && j == 1, "", "")
}
