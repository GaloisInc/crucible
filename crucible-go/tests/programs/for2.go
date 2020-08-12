package for2

import "github.com/GaloisInc/go-crucible"

func main() {
	counter := 0
	for i := 0; i < 5; i++ {
		if i % 2 == 0 {
			continue
		} else {
			for j := 0; j < 300; j++ {
				if j <= i {
					continue
				} else {
					counter += j
					break
					counter++
				}
			}
		}
	}
	crucible.Assert(counter == 6, "", "")
}
