package goto1

// import "github.com/GaloisInc/go-crucible"

func main() {
	goto Label1
	panic("impossible")
Label1:
	print("hello")
}
