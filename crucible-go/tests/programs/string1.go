package string1

// This doesn't work yet because string indexing isn't implemented.

func main() {
	var s string = "hello"
	for _, x := range s {
		print(x, " ")
	}
}
