package goto1

func main() {
	goto Label1
	panic("impossible")
Label1:
	print("hello")
}
