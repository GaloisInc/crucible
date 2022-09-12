#ifdef __cplusplus
extern "C" {
#endif

#include "crucible.h"
#include "assert.h"

#define STB_IMAGE_IMPLEMENTATION

#include "../stb_image.h"


int main() // int  argc, char* argv[])
{
    int x, y, channels;

    // if (argc != 2) {
    //     printf("Usage: %s <image size>\n", argv[0]);
    //     return 1;
    // }

    // int size_ = atoi(argv[1]);

    const int size = 16;
    uint8_t* data = malloc(size);
    assuming(data != NULL);
    for (int i = 0; i < size; i++) {
        char buf[100];
        memset(buf, 0, 100);
        strcpy(buf, "data_");
        char* bufp = buf + strlen(buf);
        assert(i < 100);
        assert(0 <= i);
        if (i < 10) {
            *bufp = '0' + i;
            bufp++;
        } else {
            *bufp = '0' + (i / 10);
            bufp++;
            *bufp = '0' + (i % 10);
            bufp++;
        }
        data[i] = crucible_uint8_t(buf);
    }

    if(!stbi_info_from_memory(data, size, &x, &y, &channels)) return 0;

    assuming(y < 0x10 && x < 0x10);

    unsigned char *img = stbi_load_from_memory(data, size, &x, &y, &channels, 4);

    free(img);
    free(data);
    free((void*) 1);

    return 0;
}

#ifdef __cplusplus
}
#endif
