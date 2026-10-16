// Evidence harness (no product source change): includes SelfModTamper.cpp with its main renamed, so that
// gen_asm (the AsmJit generator of the dynamic kernel) can be called without administrator rights or the WinRing0 driver.
//   smc_harness.exe --dump-dyn <file>   writes the generated machine code bytes to <file>
#define main smt_product_main
#include "../../SelfModTamper/SelfModTamper.cpp"
#undef main

int main(int argc, char** argv) {
	if (argc == 3 && std::string(argv[1]) == "--dump-dyn") {
		size_t codeSize = 0;
		TPCompFunc fn = gen_asm(codeSize);
		if (!fn) return 2;
		FILE* f = nullptr;
		if (fopen_s(&f, argv[2], "wb") != 0 || !f) return 3;
		fwrite((const void*)fn, 1, codeSize, f);
		fclose(f);
		printf("code size: %zu bytes\n", codeSize);
		return 0;
	}
	return 1;
}
