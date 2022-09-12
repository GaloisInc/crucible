INCLUDES = -I..
CFLAGS = -Wno-pointer-to-int-cast -Wno-int-to-pointer-cast -DSTB_DIVIDE_TEST
CPPFLAGS = -Wno-write-strings -DSTB_DIVIDE_TEST

# Uncomment this line for reproducing OSS-Fuzz bugs with image_fuzzer
#CFLAGS += -O -fsanitize=address 

all:
	$(CC) $(INCLUDES) $(CFLAGS) fuzz_main.c stbi_read_fuzzer.c -lm -o image_fuzzer
