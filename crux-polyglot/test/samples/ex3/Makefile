all : main

main : main.o helper.o
	$(CC) -o main main.o helper.o

main.o : main.c
	$(CC) -c -o main.o main.c

helper.o : helper.c
	$(CC) -c -o helper.o helper.c
