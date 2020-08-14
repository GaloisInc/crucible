package tuple1

import "github.com/GaloisInc/go-crucible"

func f() (a float64, b int64, c string) {
	return a, b, c
}

func g() (a float64, b int64, c string) {
	return
}

func h() (a int64, b int64, c string) {
	a = 1
	b = 2
	c = "c"
	return b, a, c
}

func main() {
	var x float64
	var y int64
	var z string
	x, y, z = f()
	crucible.Assert(x == 0.0 && y == 0 && z == "", "", "")
	
	a, b, c := g()
	crucible.Assert(a == x && b == y && c == z, "", "")

	_, b, c = h()
	crucible.Assert(b == 1 && c == "c", "", "")
}
