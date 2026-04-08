// SelfModTamper.cpp : This file contains the 'main' function. Program execution begins and ends there.
//

#include <iostream>
#include <fstream>
#include <vector>
#include <Windows.h>
//#include <realtimeapiset.h>
//#include <timeapi.h>
#include <time.h>
#include <inttypes.h> // uint32_t, uint8_t
#include <intrin.h>

#include <asmjit/x86.h>
#include <functional>
#include <map>

using namespace asmjit;

class TimeVariant
{
public:
	virtual void startTimer() = 0;
	virtual DWORD64 endTimer() = 0;
};

class RDTSCTime : public TimeVariant
{
	DWORD64 tsc = 0;
public:
	void startTimer() {
		tsc = __rdtsc();
	}
	DWORD64 endTimer() {
		return __rdtsc() - tsc;
	}
};

class RDTSCPTime : public TimeVariant
{
	DWORD64 tsc = 0;
	unsigned int aux;
public:
	void startTimer() {
		tsc = __rdtscp(&aux);
	}
	DWORD64 endTimer() {
		return __rdtscp(&aux) - tsc;
	}
};

class InterruptTime : public TimeVariant
{
	ULONGLONG tsc = 0;
public:
	void startTimer() {
		QueryInterruptTimePrecise(&tsc);
	}
	DWORD64 endTimer() {
		ULONGLONG t;
		QueryInterruptTimePrecise(&t);
		return t - tsc;
	}
};

class PerformanceCounterTime : public TimeVariant
{
	LARGE_INTEGER ticks = {};
	LARGE_INTEGER freq;
public:
	PerformanceCounterTime() {
		QueryPerformanceFrequency(&freq); //counts per second if converting from ticks to seconds
	}
	void startTimer() {
		QueryPerformanceCounter(&ticks);
	}
	DWORD64 endTimer() {
		LARGE_INTEGER t;
		QueryPerformanceCounter(&t);
		return t.QuadPart - ticks.QuadPart;
	}
};

class UTCTime : public TimeVariant
{
	ULARGE_INTEGER time;
public:
	void startTimer() {
		FILETIME ft;
		GetSystemTimePreciseAsFileTime(&ft);
		time.HighPart = ft.dwHighDateTime;
		time.LowPart = ft.dwLowDateTime;
	}
	DWORD64 endTimer() {
		FILETIME ft;
		ULARGE_INTEGER t;
		GetSystemTimePreciseAsFileTime(&ft);
		t.HighPart = ft.dwHighDateTime;
		t.LowPart = ft.dwLowDateTime;
		return t.QuadPart - time.QuadPart;
	}
};

class TickCountTime : public TimeVariant
{
	ULONGLONG tsc = 0;
public:
	void startTimer() {
		tsc = GetTickCount64();
	}
	DWORD64 endTimer() {
		return GetTickCount64() - tsc;
	}
};

class MultimediaTime : public TimeVariant
{
	DWORD time = 0;
public:
	MultimediaTime() {
		timeBeginPeriod(1);
	}
	~MultimediaTime() {
		timeEndPeriod(1);
	}
	void startTimer() {
		time = timeGetTime();
	}
	DWORD64 endTimer() {
		return timeGetTime() - time;
	}
};


typedef void (__cdecl *TPCompFunc)(LPVOID, ULONG64, LPVOID);
//SET PATH=%PATH%;%ProgramFiles%\CMake\bin
//D:\libraries\asmjit-master\tools\configure-vs2022-x64.bat
//cd /D D:\libraries\asmjit-master\build_vs2022_x64
//cmake --build .
//cd /D D:\libraries\asmtk-master
//cmake . -B "build_vs2022_x64" -G"Visual Studio 17" -A x64 -DASMTK_TEST=1 -DASMJIT_DIR=D:\libraries\asmjit-master\
//cd /D D:\libraries\asmtk-master\build_vs2022_x64
//cmake --build .
//https://asmjit.com/asmgrid/ AsmGrid^{BETA}
//(?<!x)(add|or|adc|sbb|and|sub|xor|cmp)\sr64\,\sr64
static void dumpCode(BaseBuilder& builder, const char* phase, FILE* f) {
	String sb;
	FormatOptions fo;
	Formatter::formatNodeList(sb, fo, &builder);
	fprintf(f, "%s:\n%s\n", phase, sb.data());
}
size_t measure_code_size(std::function<void(x86::Builder&)> f) {
	JitRuntime rt;
	CodeHolder code;
	code.init(rt.environment());
	x86::Builder cb(&code);
	f(cb);
	cb.finalize();
	return code.codeSize();
}
TPCompFunc gen_asm(size_t& codeSize)
{
	JitRuntime rt;
	CodeHolder code;
	code.init(rt.environment());
	x86::Builder cb(&code);
	const size_t PAGE_SIZE = 4096;
	const size_t num_pages = 2;
	//x86::Assembler a(&code);
	//a.mov(x86::eax, 1);
	//a.ret();
	//0x1b+0x1e+0x17==0x50 bytes total
	//cb.align(AlignMode::kCode, 64); //64 is maximum...
	auto intro_gen = [](x86::Builder& cbi, Label* lbl, size_t max_page, size_t introbytes, size_t code_size) {
		cbi.push(x86::rbx);
		cbi.push(x86::rsi);
		cbi.push(x86::rdi);
		cbi.mov(x86::rdi, x86::rdx);
		cbi.xor_(x86::rbx, x86::rbx);
		if (lbl) cbi.bind(*lbl);
		cbi.sub(x86::rdi, max_page * 8 * num_pages);
		Label skip = cbi.newLabel();
		cbi.short_().jg(skip);
		cbi.add(x86::rdi, max_page * 8 * num_pages);
		cbi.shr(x86::rdi, 3);
		cbi.dec(x86::rdi);
		cbi.imul(x86::rsi, x86::rdi, code_size);
		for (size_t i = 1; i < num_pages; i++) {
			cbi.cmp(x86::rdi, max_page*i);
			Label s = cbi.newLabel();
			cbi.short_().jl(s);
			cbi.add(x86::esi, PAGE_SIZE - max_page * code_size - (i == 1 ? introbytes : 0));
			cbi.bind(s);
		}
		cbi.mov(x86::rax, PAGE_SIZE * num_pages - (PAGE_SIZE - max_page * code_size) - introbytes + 5 - 5 - code_size + 4);
		cbi.sub(x86::rax, x86::rsi);
		cbi.shl(x86::rax, 8);
		cbi.mov(x86::rdi, 0x00000000e9ULL ^ 0x4808498D48ULL); //jmp/e9 disp32 replaces 48 8D 49 08 lea rcx,[rcx+8] followed by 48
		cbi.xor_(x86::rdi, x86::rax);
		Label lblCode = cbi.newLabel();
		Label lblXchg = cbi.newLabel();
		cbi.add(x86::dword_ptr(lblXchg, -4), x86::esi);
		cbi.xor_(x86::qword_ptr(lblCode, (int32_t)(code_size-4)), x86::rdi);
		cbi.bind(lblXchg);
		cbi.sub(x86::dword_ptr(lblXchg, -4), x86::esi);
		cbi.bind(skip);
		/*cbi.rdtscp();
		cbi.shl(x86::rdx, 32);
		cbi.or_(x86::rax, x86::rdx);
		cbi.push(x86::rax);*/
		cbi.clc();
		cbi.bind(lblCode);
	};
	auto code_gen = [](x86::Builder& cb, Label* lbl, Label* destlbl) {
		if (lbl) cb.bind(*lbl);
		cb.adc(x86::rbx, x86::ptr(x86::rcx));
		cb.sets(x86::dl);
		cb.setp(x86::al);
		cb.shl(x86::al, 2);
		cb.or_(x86::dl, x86::al);
		cb.shl(x86::dl, 3);
		cb.xor_(destlbl ? x86::byte_ptr(*destlbl, 1) : x86::byte_ptr(x86::rip, PAGE_SIZE), x86::dl); //add 1 to skip the prefix byte
		cb.lea(x86::rcx, x86::ptr(x86::rcx, 8));
	};
	const size_t introbytes = measure_code_size([&intro_gen](x86::Builder& cbi) { intro_gen(cbi, nullptr, MAXCHAR, MAXCHAR, MAXCHAR); });
	const size_t code_size = measure_code_size([&code_gen](x86::Builder& cb) { code_gen(cb, nullptr, nullptr); });
	const size_t max_page = (PAGE_SIZE - introbytes) / code_size;
	printf("Number of pages: %zu Unrolled loop size per page: %zu Intro bytes: 0x%zX Code size: 0x%zX\n", num_pages, max_page, introbytes, code_size);
	Label xchglbl;
	Label next = cb.newLabel();
	intro_gen(cb, &next, max_page, introbytes, code_size);
	std::vector<Label> labels;
	size_t i;
	for (i = max_page*num_pages; i != 0; i--)
		labels.push_back(cb.newLabel());
	for (int j = 0; j < num_pages; j++) {
		for (i = 0; i < max_page; i++) {
			code_gen(cb, &labels[i + j * max_page], &labels[(i + (j + num_pages - 1) * max_page) % (max_page * num_pages)]);
		}
		if (j != num_pages - 1) {
			i = (j == 0 ? introbytes : 0) + max_page * code_size;
			while (i < PAGE_SIZE) { cb.nop(); i++; }
		}
	}
	cb.jmp(next);
	Label lblXchg = cb.newLabel();
	cb.add(x86::dword_ptr(lblXchg, -4), x86::esi);
	cb.xor_(x86::qword_ptr(labels[0], (int32_t)(code_size - 4)), x86::rdi);
	cb.bind(lblXchg);
	cb.sub(x86::dword_ptr(lblXchg, -4), x86::esi);
	cb.mov(x86::qword_ptr(x86::r8), x86::rbx);
	/*cb.rdtscp();
	cb.shl(x86::rdx, 32);
	cb.or_(x86::rax, x86::rdx);
	cb.pop(x86::rbx);
	cb.sub(x86::rax, x86::rbx);*/
	cb.pop(x86::rdi);
	cb.pop(x86::rsi);
	cb.pop(x86::rbx);
	cb.ret();
	FILE* f = nullptr;
	fopen_s(&f, "func.asm", "w");
	if (f != nullptr) {
		dumpCode(cb, "Raw Function", f);
		fclose(f);
	}
	cb.finalize();
	TPCompFunc fn;
	Error err = rt.add(&fn, &code);
	//printf("Code size: %llX", code.codeSize());
	if (err) {
		printf("AsmJit failed: %s\n", DebugUtils::errorAsString(err));
		return nullptr;
	}
	//ULONG64 result = fn(pData, ulSize, pResult);
	//printf("%llX\n", result);
	rt.release(fn);
	codeSize = code.codeSize();
	TPCompFunc buf = (TPCompFunc)VirtualAlloc(NULL, codeSize, MEM_RESERVE | MEM_COMMIT, PAGE_EXECUTE_READWRITE);
	if (buf) memcpy(buf, fn, codeSize);
	return buf;
}

//extern "C" TPCompFunc TPComp;
extern "C" void __cdecl TPComp(LPVOID, ULONG64, LPVOID);
extern "C" void __cdecl TPCompLoop(LPVOID, ULONG64, LPVOID);

uint32_t CRCTable[256] = {};

void generate_CRC_table_be() //little endian
{
	//x^32+x^26+x^23+x^22+x^16+x^12+x^11+x^10+x^8+x^7+x^5+x^4+x^2+x+1 = 0000 0100 1100 0001 0001 1101 1011 0111 (1) = 0x04C11DB7, big endian=0xEDB88320
	CRCTable[0] = 0;
	uint32_t crc = 1;
	uint8_t i = 128;
	do {
		if (crc & 1) {
			crc = (crc >> 1) ^ 0xEDB88320; //CRC polynomial
		}
		else {
			crc >>= 1;
		}
		for (uint16_t j = 0; j < 256; j += i << 1) {
			CRCTable[i + j] = crc ^ CRCTable[j];
		}
		i >>= 1;
	} while (i > 0);
}

//https://en.wikipedia.org/wiki/Cyclic_redundancy_check
uint32_t CRC32(const uint8_t data[], size_t data_length) {
	uint32_t crc32 = 0xFFFFFFFFu;

	for (size_t i = 0; i < data_length; i++) {
		const uint32_t lookupIndex = (crc32 ^ data[i]) & 0xff;
		crc32 = (crc32 >> 8) ^ CRCTable[lookupIndex];  // CRCTable is an array of 256 32-bit constants
	}

	// Finalize the CRC-32 value by inverting all the bits
	crc32 ^= 0xFFFFFFFFu;
	return crc32;
}

#include <Psapi.h>
#pragma comment(lib, "psapi")

HMODULE GetModuleBase(HANDLE hProc, const std::wstring& sModuleName)
{
	HMODULE* hModules = NULL;
	DWORD cModules;
	std::vector<wchar_t> buffer;
	EnumProcessModules(hProc, hModules, 0, &cModules);
	hModules = new HMODULE[cModules / sizeof(HMODULE)];
	if (EnumProcessModules(hProc, hModules, cModules, &cModules)) {
		for (size_t i = 0; i < cModules / sizeof(HMODULE); i++) {
			buffer.resize(MAX_PATH);
			if (GetModuleBaseName(hProc, hModules[i], (LPWSTR)buffer.data(), (DWORD)buffer.size())) {
				std::wstring str(buffer.data());
				if (str == sModuleName) {
					HMODULE found = hModules[i];
					delete[] hModules;
					return found;
				}
			}
		}
	}
	delete[] hModules;
	return NULL;
}

void GetCodeSegmentBaseSize(PBYTE & base, DWORD & size)
{
	HANDLE hProcess = GetCurrentProcess();
	/*std::vector<wchar_t> sBuf;
	sBuf.resize(MAX_PATH);
	GetModuleFileName(NULL, (LPWSTR)sBuf.data(), sBuf.size()); //GetProcessImageFileName
	std::wstring sModuleNameStr(sBuf.data());
	std::string::size_type pos = sModuleNameStr.rfind('\\');
	if (pos != std::string::npos)
		sModuleNameStr = sModuleNameStr.substr(pos + 1);
	HMODULE hModule = GetModuleBase(hProcess, sModuleNameStr);*/
	HMODULE hModule = GetModuleHandle(NULL);
	MODULEINFO mi = {};
	GetModuleInformation(hProcess, hModule, &mi, sizeof(MODULEINFO));
	IMAGE_DOS_HEADER dosHeader;
	union {
		IMAGE_NT_HEADERS ntHeader;
		IMAGE_NT_HEADERS32 ntHeader32;
		IMAGE_NT_HEADERS64 ntHeader64;
	};
	if (ReadProcessMemory(hProcess, mi.lpBaseOfDll, &dosHeader, sizeof(dosHeader), NULL) &&
		dosHeader.e_magic == IMAGE_DOS_SIGNATURE) {
		if (ReadProcessMemory(hProcess, (PBYTE)mi.lpBaseOfDll + dosHeader.e_lfanew, &ntHeader, sizeof(ntHeader), 0) &&
			ntHeader.Signature == IMAGE_NT_SIGNATURE) {
			PIMAGE_SECTION_HEADER pSection = IMAGE_FIRST_SECTION((PIMAGE_NT_HEADERS)((PBYTE)mi.lpBaseOfDll + dosHeader.e_lfanew));
			for (DWORD n = 0; n < ntHeader.FileHeader.NumberOfSections; n++) {
				//printf("%.8s\n", (pSection + n)->Name);
				if (strcmp((const char*)(pSection + n)->Name, ".text") == 0) {
					base = (PBYTE)mi.lpBaseOfDll + (pSection + n)->VirtualAddress;
					size = (pSection + n)->SizeOfRawData;
					return;
				}
			}
			/*PIMAGE_DATA_DIRECTORY dataDirectory = 0;
			switch (ntHeader.OptionalHeader.Magic) {
			case IMAGE_NT_OPTIONAL_HDR32_MAGIC:
				dataDirectory = ntHeader32.OptionalHeader.DataDirectory;
				break;
			case IMAGE_NT_OPTIONAL_HDR64_MAGIC:
				dataDirectory = ntHeader64.OptionalHeader.DataDirectory;
				break;
			}
			if (dataDirectory) {}*/
		}
	}
}

bool parity(unsigned __int64 v)
{
	bool parity = false;  // parity will be the parity of v

	while (v)
	{
		parity = !parity;
		v = v & (v - 1);
	}
	return parity;
}

inline bool paritybyte(unsigned char v)
{
	v ^= v >> 4;
	v &= 0xf;
	return (0x6996 >> v) & 1;
}

void __cdecl TPCompC(PULONG64 pData, ULONG64 ulSize, PULONG64 pResult)
{
	unsigned __int64 sum = 0;
	static unsigned char op = 0;
	const PBYTE pTPCompOffset = (PBYTE)TPComp + 5 + *(PULONG32)((PBYTE)TPComp + 1); //C compiler makes this point to a jump instruction E9 offs32
	const size_t offsetInFunc = 0xF; //manually found based on MOV, LEA, XOR, CLC, ADC prefix
	const PULONG64 pModOffset = (PULONG64)((ULONG64)((PBYTE)pTPCompOffset + offsetInFunc) & ~0x7ULL);
	const unsigned char pModByteOffset = ((ULONG64)((PBYTE)pTPCompOffset + offsetInFunc) & 7) * 8+3; //convert to bits, add 3 bits for the ADC/SBB/XOR/CMP offset
	const unsigned __int64 preserve = ~(5ULL << pModByteOffset);
	for (LPBYTE pEnd = (LPBYTE)pData + ulSize; (LPBYTE)pData < pEnd; pData++) {
		unsigned __int64 res;
		unsigned __int64 pDataVal = pData == pModOffset ? (*pData & preserve) | ((unsigned __int64)op << pModByteOffset) : *pData;
		switch (op) {
		case 0: res = sum += pDataVal; break;
		case 1: res = sum -= pDataVal; break;
		case 4: res = sum ^= pDataVal; break;
		case 5: res = sum - pDataVal; break;
		default: res = 0;
		}
		op ^= (!paritybyte((unsigned char)res) << 2) | ((res & 0x8000000000000000ULL) != 0);
	}
	*pResult = sum;
}
#define __attribute__(x) //__attribute__ in GCC/Clang only
template< unsigned N > struct CodeRepeat {
	static void generate() __attribute__((always_inline)) {
		//__asm__ volatile ("nop");
		CodeRepeat< N - 1 >::generate();
	}
};
template<> struct CodeRepeat<0> { static inline void generate() {} };

#define ten(a)     a;a;a;a;a;a;a;a;a;a
#define hundred(a) ten(ten(a))

void __cdecl TPCompCLoop(PULONG64 pData, ULONG64 ulSize, PULONG64 pResult)
{
	unsigned __int64 sum = 0;
	const size_t numPages = 2;
	const unsigned int loopLength = 148;
	static unsigned char op[numPages * loopLength] = {};
	const PBYTE pTPCompOffset = (PBYTE)TPCompLoop + 5 + *(PULONG32)((PBYTE)TPCompLoop + 1); //C compiler makes this point to a jump instruction E9 offs32
	size_t offsetInFunc = 0x60; //manually found based on MOV, LEA, XOR, CLC, ADC prefix
	const size_t code_size = 0x1b;
	struct ByteLCIndices {
		unsigned char byteidx;
		unsigned int idx;
	};
	std::map<PULONG64, ByteLCIndices> adjustOffsets;
	for (unsigned int i = 0; i < loopLength; i++)
		adjustOffsets.insert(std::pair<PULONG64, ByteLCIndices>((PULONG64)((ULONG64)((PBYTE)pTPCompOffset + offsetInFunc + code_size * i) & ~0x7ULL),
			ByteLCIndices{ (unsigned char)((ULONG64)((PBYTE)pTPCompOffset + offsetInFunc + code_size * i) & 7), i }));
	const size_t PAGE_SIZE = 4096;
	offsetInFunc = PAGE_SIZE + 1;
	for (unsigned int i = 0; i < loopLength; i++) {
		adjustOffsets.insert(std::pair<PULONG64, ByteLCIndices>((PULONG64)((ULONG64)((PBYTE)pTPCompOffset + offsetInFunc + code_size * i) & ~0x7ULL),
			ByteLCIndices{ (unsigned char)((ULONG64)((PBYTE)pTPCompOffset + offsetInFunc + code_size * i) & 7), i+loopLength }));
	}
	const PULONG64 pModOffset = (PULONG64)((ULONG64)((PBYTE)pTPCompOffset + offsetInFunc) & ~0x7ULL);
	//convert to bits, add 3 bits for the ADC/SBB/XOR/CMP offset
	const unsigned __int64 preserve[8] = { ~(5ULL << (0 * 8 + 3)), ~(5ULL << (1 * 8 + 3)), ~(5ULL << (2 * 8 + 3)), ~(5ULL << (3 * 8 + 3)),
		~(5ULL << (4 * 8 + 3)), ~(5ULL << (5 * 8 + 3)), ~(5ULL << (6 * 8 + 3)), ~(5ULL << (7 * 8 + 3)) };
	size_t lc = 0;
	for (LPBYTE pEnd = (LPBYTE)pData + ulSize; (LPBYTE)pData < pEnd; pData++, lc++) {
		if (lc == numPages * loopLength) lc = 0;
		//CodeRepeat<loopLength>::generate();
		unsigned __int64 res;
		auto hasOffset = adjustOffsets.find(pData);
		unsigned __int64 pDataVal = hasOffset != adjustOffsets.end() ? (*pData & preserve[hasOffset->second.byteidx]) | ((unsigned __int64)op[hasOffset->second.idx] << (hasOffset->second.byteidx * 8 + 3)) : *pData;
		//unsigned __int64 pDataVal = *pData;
		switch (op[lc]) {
		case 0: res = sum += pDataVal; break;
		case 1: res = sum -= pDataVal; break;
		case 4: res = sum ^= pDataVal; break;
		case 5: res = sum - pDataVal; break;
		default: res = 0;
		}
		op[(lc + (numPages - 1) * loopLength) % (numPages * loopLength)] ^= (!paritybyte((unsigned char)res) << 2) | ((res & 0x8000000000000000ULL) != 0);
	}
	*pResult = sum;
}

#define IA32_PMC0 0xC1
#define IA32_PERFEVTSEL0 0x186
#define IA32_PERF_GLOBAL_CTRL 0x38F

#define AMD64_PERFCTR0 0xC0010004
#define AMD64_PERFEVTSEL0 0xC0010000
#define AMD64_PERFCNTRGLOBALCTL 0xC0000301

#define PERFEVTSEL_USR (1 << 16)
#define PERFEVTSEL_OS (1 << 17)
#define PERFEVTSEL_EDGE (1 << 18)
#define PERFEVTSEL_EN (1 << 22)
#define PERFEVTSEL_INV (1 << 23)
#define MACHINE_CLEARS 0xC3 //Intel
#define MACHINE_CLEARS_SMC 0x4
#define PIPELINE_RESTART_DUE_TO_SELF_MODIFYING_CODE 0x21 //AMD

#define OLS_TYPE 40000
#define IOCTL_OLS_READ_MSR \
	CTL_CODE(OLS_TYPE, 0x821, METHOD_BUFFERED, FILE_ANY_ACCESS)

#define IOCTL_OLS_WRITE_MSR \
	CTL_CODE(OLS_TYPE, 0x822, METHOD_BUFFERED, FILE_ANY_ACCESS)

#define IOCTL_OLS_READ_PMC \
	CTL_CODE(OLS_TYPE, 0x823, METHOD_BUFFERED, FILE_ANY_ACCESS)


bool writeMSR(HANDLE hDevice, DWORD address, unsigned long long value)
{
	DWORD bytesReturned = 0;
	DWORD dwIoControlCode = IOCTL_OLS_WRITE_MSR;
	DWORD inBuffer[3];
	inBuffer[0] = address;
	*((unsigned long long*)&inBuffer[1]) = value;
	return DeviceIoControl(hDevice, dwIoControlCode, inBuffer, sizeof(inBuffer), NULL,
		0, &bytesReturned, NULL);
}

unsigned long long readMSR(HANDLE hDevice, DWORD address, bool isPMC)
{
	DWORD bytesReturned = 0;
	DWORD dwIoControlCode = isPMC ? IOCTL_OLS_READ_PMC : IOCTL_OLS_READ_MSR;
	unsigned long long outBuffer = 0;
	if (!DeviceIoControl(hDevice, dwIoControlCode, &address, sizeof(address),
		&outBuffer, sizeof(outBuffer), &bytesReturned, NULL) ||
		bytesReturned != sizeof(outBuffer)) return -1;
	return outBuffer;
}

void loadSMCPerfCounter(HANDLE hDevice)
{
	unsigned long long curPerfSetting = readMSR(hDevice, IA32_PERFEVTSEL0, false);
	if (curPerfSetting != 0) return; //presumably it is already in use
	//unsigned long long curGlobCtrl = readMSR(hDevice, IA32_PERF_GLOBAL_CTRL, false);
	//printf("%llX\n", curGlobCtrl); //0x70000000F by default so all are enabled
	//curGlobCtrl |= 1;
	//writeMSR(hDevice, IA32_PERF_GLOBAL_CTRL, curGlobCtrl);
	//Event Num. Umask Value Event Mask Mnemonic
	//MACHINE_CLEARS.SMC supported on Coffee Lake
	writeMSR(hDevice, IA32_PERFEVTSEL0, MACHINE_CLEARS | (MACHINE_CLEARS_SMC << 8) | PERFEVTSEL_USR | PERFEVTSEL_EN);
	//curPerfSetting = readMSR(hDevice, IA32_PERFEVTSEL0, false);
	//printf("%llX\n", curPerfSetting);
}

void resetPerfCounter(HANDLE hDevice)
{
	//unsigned long long curGlobCtrl = readMSR(hDevice, IA32_PERF_GLOBAL_CTRL, false);
	//curGlobCtrl &= ~1ULL;
	//writeMSR(hDevice, IA32_PERF_GLOBAL_CTRL, curGlobCtrl);
	writeMSR(hDevice, IA32_PERFEVTSEL0, 0x0);
}

HANDLE enablePerfCounters(std::wstring id, std::wstring filename)
{
	int manufacturerInfo[4];
	__cpuid(manufacturerInfo, 0);
	int procInfo[4];
	__cpuid(procInfo, 1);
	DWORD model = ((procInfo[0] >> 4) & 0xF) | ((procInfo[0] >> 12) & 0xF0);
	DWORD family = ((procInfo[0] >> 8) & 0xF) | ((procInfo[0] >> 16) & 0xFF0);
	int perfInfo[4];
	__cpuid(perfInfo, 0xA); // If CPUID.0AH: EAX[15:8] > 1 or # of IA32_PMC MSRs per logical processor
	printf("Manufacturer: %.4s%.4s%.4s\n", (char*) & manufacturerInfo[1], (char*)&manufacturerInfo[3], (char*)&manufacturerInfo[2]); //"GenuineIntel"
	printf("DisplayModel: 0x%X DisplayFamily: 0x%X\n", model, family); //DisplayModel: 0x9E DisplayFamily: 0x6 Coffee Lake
	DWORD versionPerf = perfInfo[0] & 0xFF;
	DWORD generalPerf = (perfInfo[0] >> 8) & 0xFF;
	DWORD bitWidthPerf = (perfInfo[0] >> 16) & 0xFF;
	printf("Architecture Performance Monitoring Version: %d Number of Performance Counters per Logical Processor: %d PMC bit width: %d\n",
		versionPerf, generalPerf, bitWidthPerf);
	SC_HANDLE hManager = OpenSCManager(NULL, NULL, SC_MANAGER_ALL_ACCESS);
	if (hManager == NULL) return NULL;
	WCHAR buf[MAX_PATH];
	GetModuleFileNameW(NULL, buf, MAX_PATH);
	std::wstring path = buf;
	const size_t slashPos = path.rfind(L'\\');
	if (slashPos != std::wstring::npos)
		path.resize(slashPos);
	path += L'\\' + filename;
	SC_HANDLE hService = CreateService(hManager, id.c_str(), id.c_str(), SERVICE_ALL_ACCESS, SERVICE_KERNEL_DRIVER,
		SERVICE_DEMAND_START, SERVICE_ERROR_NORMAL, path.c_str(), NULL, NULL, NULL, NULL, NULL);
	if (hService == NULL && GetLastError() == ERROR_SERVICE_EXISTS) {
		hService = OpenService(hManager, id.c_str(), SERVICE_ALL_ACCESS);
	}
	if (hService == NULL) {
		CloseServiceHandle(hManager);
		return NULL;
	}
	if (!StartService(hService, 0, NULL)) {
		if (GetLastError() != ERROR_SERVICE_ALREADY_RUNNING) {
			CloseServiceHandle(hService);
			CloseServiceHandle(hManager);
			return NULL;
		}
	}
	CloseServiceHandle(hService);
	CloseServiceHandle(hManager);
	HANDLE hDevice = CreateFile((L"\\\\.\\" + id).c_str(), GENERIC_READ | GENERIC_WRITE, 0, NULL, OPEN_EXISTING,
		FILE_ATTRIBUTE_NORMAL, NULL);

	loadSMCPerfCounter(hDevice);

	return hDevice;
}

void disablePerfCounters(std::wstring id, HANDLE hDevice)
{
	if (hDevice) {
		resetPerfCounter(hDevice);
		CloseHandle(hDevice);
	}
	SC_HANDLE hManager = OpenSCManager(NULL, NULL, SC_MANAGER_ALL_ACCESS);
	if (hManager == NULL) return;
	SC_HANDLE hService = OpenService(hManager, id.c_str(), SERVICE_ALL_ACCESS);
	if (!hService) {
		CloseServiceHandle(hManager);
		return;
	}
	SERVICE_STATUS status = {};
	ControlService(hService, SERVICE_CONTROL_STOP, &status);
	DeleteService(hService);
	CloseServiceHandle(hService);
	CloseServiceHandle(hManager);
}

bool zeroSMCCount(HANDLE hDevice)
{
	return writeMSR(hDevice, IA32_PMC0, 0x0);
}

unsigned long long getSMCCount(HANDLE hDevice)
{
	return readMSR(hDevice, 0x0, true) & ((1ULL<<48)-1);
	//return readMSR(hDevice, IA32_PMC0, false) & ((1ULL<<48)-1);
	//return __readpmc(0x0); //requires CR4.PCE Performonce-monitoring Counters Enabled from protected/virtual 8086 mode
}

void useExtraData();
int main()
{
	SYSTEM_INFO si;
	GetSystemInfo(&si);
	SetThreadAffinityMask(GetCurrentThread(), 1); //attach to a single logical processor for performance monitoring
	SetPriorityClass(GetCurrentProcess(), REALTIME_PRIORITY_CLASS);
	SetThreadPriority(GetCurrentThread(), THREAD_PRIORITY_TIME_CRITICAL);
	std::wstring id = L"WinRing0_1_2_0";
	disablePerfCounters(id, NULL);
	HANDLE hDevice = enablePerfCounters(id, L"WinRing0x64.sys");
	//useExtraData();
	printf("The page size for this system is %u bytes.\n", si.dwPageSize);
	generate_CRC_table_be();
	PBYTE base = 0;
	DWORD size = 0;
	GetCodeSegmentBaseSize(base, size);
	printf("Code segment base: 0x%llX size: 0x%lX End address: 0x%llX\n", (ULONG64)base, size, (ULONG64)(base + size));

	//printf("%X\n", CRC32((const unsigned char*)"ABCDEFGHIJKLMNOPQRSTUVWXYZ", 1));
	ULONG64 checksum = 0;
	//unreliable ticks in CPU frequency, ticks in CPU frequency, milliseconds, 100ns units, ticks in Frequency ticks/second, milliseconds
	TimeVariant* allTimers[] = { new RDTSCTime(), new RDTSCPTime(), new InterruptTime(), new PerformanceCounterTime(), new UTCTime(), new TickCountTime(), new MultimediaTime() };
	const size_t numTimers = sizeof(allTimers) / sizeof(TimeVariant*);
	size_t codeSize;
	TPCompFunc TPCompF = gen_asm(codeSize);
	VirtualLock(TPCompF, codeSize);
	TPCompFunc testFuncs[] = { (TPCompFunc)TPCompC, TPComp, (TPCompFunc)TPCompCLoop, TPCompF, TPCompLoop };
	const char* strFuncNames[] = { "C", "SMC", "C Loop", "SMC Loop", "Dyn SMC Loop" };
	const size_t trials = 10000;
	std::ofstream out_file("out.txt");
	for (size_t f = 0; f < sizeof(testFuncs) / sizeof(TPCompFunc); f++) {
		std::cout << strFuncNames[f] << std::endl;
		ULONG64 avgTimeVals[numTimers] = {};
		ULONG64 minTimeVals[numTimers] = {};
		ULONG64 maxTimeVals[numTimers] = {};
		zeroSMCCount(hDevice);
		ULONG64 smcClears = getSMCCount(hDevice);
		for (size_t i = 0; i < trials; i++) {
			ULONG64 checksum = 0;
			ULONG64 timeVals[numTimers] = {};
			for (size_t j = 0; j < numTimers; j++)
				allTimers[j]->startTimer();
			testFuncs[f]((PULONG64)base, size, &checksum);
			std::cout << "MACHINE_CLEARS.SMC: " << (getSMCCount(hDevice) - smcClears) << std::endl;
			for (size_t j = 0; j < numTimers; j++) {
				timeVals[j] = allTimers[j]->endTimer();
			}
			for (size_t j = 0; j < numTimers; j++) {
				if (f == 1 && j == 1) out_file << timeVals[j] << ", ";
				avgTimeVals[j] += timeVals[j];
				minTimeVals[j] = (i == 0) ? timeVals[j] : min(timeVals[j], minTimeVals[j]);
				maxTimeVals[j] = max(timeVals[j], maxTimeVals[j]);
			}
			//std::cout << checksum << std::endl;
		}
		for (size_t j = 0; j < numTimers; j++) {
			std::cout << (avgTimeVals[j] / trials) << " " << minTimeVals[j] << " " << maxTimeVals[j] << std::endl;
		}
		std::cout << "MACHINE_CLEARS.SMC: " << (getSMCCount(hDevice) - smcClears) << std::endl;
		std::cout << std::endl;
	}
	disablePerfCounters(id, hDevice);
	for (size_t i = 0; i < numTimers; i++) delete allTimers[i];
	VirtualUnlock(TPCompF, codeSize);
	VirtualFree(TPCompF, 0, MEM_RELEASE);
}

#pragma const_seg(push, ".text")
const char* extraData = "0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789";
#pragma const_seg(pop)
void useExtraData() {
	printf("%s\n", extraData);
}