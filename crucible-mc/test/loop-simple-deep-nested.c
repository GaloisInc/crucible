extern void abort(void);
void reach_error(){}

int main() {
	unsigned a, b, c, d, e;

	unsigned uint32_max;
	uint32_max = 0xffffffff;

	for (a = 0; a < uint32_max - 1; ++a) {
		for (b = 0; b < uint32_max - 1; ++b) {
			for (c = 0; c < uint32_max - 1; ++c) {
				for (d = 0; d < uint32_max - 1; ++d) {
					for (e = 0; e < uint32_max - 1; ++e) {
						if ((a == b) && (b == c) && (c == d) && (d == e) && (e == (uint32_max - 2))) {
							{
								reach_error();
								abort();
							}
						}
					}
				}
			}
		}
	}

	return 0;
}
