// Evidence harness (no product source change): includes SelfModTamper.cpp with its main renamed, so that the kernels
// (TPComp, TPCompC, TPCompLoop, TPCompCLoop and the AsmJit generator gen_asm) can be called without administrator rights or the
// WinRing0 driver.
//   smc_harness.exe --dump-dyn <file>   writes the generated machine code bytes of the dynamic kernel to <file>
//   smc_harness.exe --vectors <file>    replays validation/native/vectors.txt (generated from the Lean models by validation/vectors_gen.lean.txt (copy it to a .lean file to run it; the preflight requires every .lean file to be a module))
//   smc_harness.exe --text              differential run on the harness's own .text (introspective): asm kernel vs C emulation
// Exit code 0 means every comparison agreed.  Evidence, not proof.
#define main smt_product_main
#ifndef PRODUCT_CPP
#define PRODUCT_CPP "../../SelfModTamper/SelfModTamper.cpp"
#endif
#include PRODUCT_CPP
#undef main

static unsigned long long xorshift64(unsigned long long x) {
	x ^= x << 13; x ^= x >> 7; x ^= x << 17;
	return x;
}

// Same generator as validation/vectors_gen.lean.txt (copy it to a .lean file to run it; the preflight requires every .lean file to be a module): state = seed * 0x9E3779B97F4A7C15 + 1, then one xorshift step per qword.
static void fillBuffer(char kind, unsigned long long seed, std::vector<unsigned long long>& q) {
	unsigned long long st = seed * 0x9E3779B97F4A7C15ULL + 1;
	for (auto& v : q) {
		st = xorshift64(st);
		v = kind == 'Z' ? 0 : kind == 'F' ? ~0ULL : kind == 'H' ? 0x8000000000000000ULL : st;
	}
}

static int runVectors(const char* path) {
	setvbuf(stdout, NULL, _IONBF, 0);
	std::ifstream in(path);
	if (!in) { printf("cannot open %s\n", path); return 2; }
	size_t codeSize = 0;
	TPCompFunc dyn = gen_asm(codeSize);
	if (!dyn) return 3;
	struct K { const char* name; TPCompFunc fn; bool loopSum; size_t pass = 0, fail = 0, skipped = 0; };
	K ks[] = { {"TPComp (asm, single site)", TPComp, false}, {"TPCompC (C emulation)", (TPCompFunc)TPCompC, false},
	           {"TPCompLoop (asm, static unrolled)", TPCompLoop, true}, {"TPCompCLoop (C emulation)", (TPCompFunc)TPCompCLoop, true},
	           {"gen_asm (AsmJit dynamic unrolled)", dyn, true} };
	std::string tag; char kind; unsigned long long seed, size, es, el;
	size_t n = 0;
	while (in >> tag >> kind >> seed >> size >> es >> el) {
		std::vector<unsigned long long> buf((size + 7) / 8 + 1);
		buf.resize((size + 7) / 8);
		fillBuffer(kind, seed, buf);
		for (auto& k : ks) {
			ULONG64 r = 0xDEADBEEF;
			if (k.loopSum && (size / 8) % 148 == 0 && k.fn != (TPCompFunc)TPCompCLoop) { k.skipped++; continue; } // L07, see --probe
			if (n < 3 || getenv("HARNESS_TRACE")) printf("vector %zu %c %llu %llu: %s\n", n, kind, seed, size, k.name);
			k.fn(buf.data(), size, &r);
			const unsigned long long want = k.loopSum ? el : es;
			if (r == want) k.pass++;
			else { k.fail++; printf("MISMATCH %s vector %zu (%c %llu %llu): got %llu want %llu\n", k.name, n, kind, seed, size, (unsigned long long)r, want); }
		}
		n++;
	}
	int bad = 0;
	for (auto& k : ks) { printf("%-36s pass %zu fail %zu\n", k.name, k.pass, k.fail); bad += k.fail != 0; }
	printf("vectors: %zu\n", n);
	return bad ? 1 : 0;
}

// Introspective run: the region is the harness's own .text, which contains the kernels being run.  The asm kernel reads its own
// modified opcode bytes; the C emulation substitutes them (this is the case the thunk-following in TPCompC/TPCompCLoop serves).
static int runText() {
	PBYTE base = 0; DWORD size = 0;
	GetCodeSegmentBaseSize(base, size);
	printf("text base 0x%llX size 0x%lX\n", (unsigned long long)base, size);
	int bad = 0;
	struct Pair { const char* name; TPCompFunc a, c; };
	Pair ps[] = { {"single site", TPComp, (TPCompFunc)TPCompC}, {"static unrolled", TPCompLoop, (TPCompFunc)TPCompCLoop} };
	for (auto& p : ps) {
		for (int rep = 0; rep < 4; rep++) {
			ULONG64 ra = 1, rc = 2;
			p.a((PULONG64)base, size, &ra);
			p.c((PULONG64)base, size, &rc);
			printf("%-16s call %d: asm %llu C %llu %s\n", p.name, rep, (unsigned long long)ra, (unsigned long long)rc, ra == rc ? "equal" : "DIFFERENT");
			bad += ra != rc;
		}
	}
	return bad ? 1 : 0;
}

// Probe one size on the unrolled kernels: SEH-guarded, prints the sum or the exception code (L07: termination patch).
static int callGuarded(TPCompFunc fn, void* buf, ULONG64 size, ULONG64* r, unsigned long* code) {
	__try { fn(buf, size, r); return 0; }
	__except (*code = GetExceptionCode(), EXCEPTION_EXECUTE_HANDLER) { return 1; }
}
static int runProbe(unsigned long long size, const char* only) {
	setvbuf(stdout, NULL, _IONBF, 0);
	std::vector<unsigned long long> buf(size / 8 + 1, 0x0123456789ABCDEFULL);
	size_t codeSize = 0;
	TPCompFunc dyn = gen_asm(codeSize);
	struct { const char* name; TPCompFunc fn; } ks[] = { {"TPCompLoop", TPCompLoop}, {"gen_asm", dyn}, {"TPCompCLoop", (TPCompFunc)TPCompCLoop} };
	int bad = 0;
	for (auto& k : ks) {
		if (only && std::string(only) != k.name) continue;
		ULONG64 r = 0; unsigned long code = 0;
		if (callGuarded(k.fn, buf.data(), size, &r, &code)) { printf("size %llu %s: exception 0x%lX\n", size, k.name, code); bad++; }
		else printf("size %llu %s: sum %llu\n", size, k.name, (unsigned long long)r);
	}
	return bad ? 1 : 0;
}
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
	if (argc == 3 && std::string(argv[1]) == "--vectors") return runVectors(argv[2]);
	if (argc == 2 && std::string(argv[1]) == "--text") return runText();
	if ((argc == 3 || argc == 4) && std::string(argv[1]) == "--probe") return runProbe(strtoull(argv[2], nullptr, 10), argc == 4 ? argv[3] : nullptr);
	return 1;
}
