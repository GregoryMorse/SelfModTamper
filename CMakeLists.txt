cmake_minimum_required(VERSION 3.21)
project(SelfModTamper LANGUAGES CXX)
if(WIN32)
    enable_language(ASM_MASM)
endif()

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# ── x64-only guard ────────────────────────────────────────────────────────────
if(NOT CMAKE_SIZEOF_VOID_P EQUAL 8)
    message(FATAL_ERROR "SelfModTamper requires a 64-bit (x64) build.")
endif()

if(NOT WIN32)
    include(cmake/posix.cmake)
    return()
endif()

# ── Dependencies (fetched by CMake from a pinned, hash-checked archive) ─────
include(cmake/asmjit.cmake)

# ── Target ────────────────────────────────────────────────────────────────────
add_executable(SelfModTamper
    SelfModTamper/SelfModTamper.cpp
    SelfModTamper/TP.asm
)

# Same compiler settings as the Visual Studio project (Unicode character set, conformance mode).
target_compile_definitions(SelfModTamper PRIVATE UNICODE _UNICODE _CONSOLE)
target_compile_options(SelfModTamper PRIVATE /permissive-)

target_link_libraries(SelfModTamper PRIVATE
    asmjit::asmjit
    psapi       # EnumProcessModules, GetModuleInformation
    winmm       # timeBeginPeriod, timeGetTime, timeEndPeriod
    mincore     # QueryInterruptTimePrecise
)

# The .text section must be read-write-execute for the static SMC variants.
target_link_options(SelfModTamper PRIVATE "/SECTION:.text,RWE")

# asmjit is linked statically (cmake/asmjit.cmake), so there are no runtime DLLs to copy.

