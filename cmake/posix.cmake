# Linux (x86-64) build of SelfModTamper: the MASM kernels in TP.asm are translated to GNU as by scripts/masm2gas.py (no extra
# assembler to install), the Windows API is replaced by SelfModTamper/platform_posix.h and the WinRing0 driver by perf_event_open.
# The dynamic (asmjit) variant is built only if asmjit is found, e.g.  cmake -DCMAKE_PREFIX_PATH=<asmjit install> ..
if(NOT CMAKE_SYSTEM_NAME STREQUAL "Linux" OR NOT CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64|AMD64")
    message(FATAL_ERROR "The POSIX build of SelfModTamper supports Linux on x86-64 only.")
endif()
enable_language(ASM)
find_package(Python3 REQUIRED COMPONENTS Interpreter)
set(TP_GAS "${CMAKE_CURRENT_BINARY_DIR}/TP.gas.S")
add_custom_command(OUTPUT "${TP_GAS}"
    COMMAND Python3::Interpreter "${CMAKE_SOURCE_DIR}/scripts/masm2gas.py" "${CMAKE_SOURCE_DIR}/SelfModTamper/TP.asm" "${TP_GAS}"
    DEPENDS "${CMAKE_SOURCE_DIR}/SelfModTamper/TP.asm" "${CMAKE_SOURCE_DIR}/scripts/masm2gas.py"
    COMMENT "Translating TP.asm (MASM) to GNU as")
add_executable(SelfModTamper SelfModTamper/SelfModTamper.cpp "${TP_GAS}")
find_package(asmjit CONFIG QUIET)
if(asmjit_FOUND)
    target_link_libraries(SelfModTamper PRIVATE asmjit::asmjit)
    target_compile_definitions(SelfModTamper PRIVATE SMC_WITH_ASMJIT)
else()
    message(STATUS "asmjit not found: the dynamic ('Dyn SMC Loop') variant is skipped")
endif()
target_compile_options(SelfModTamper PRIVATE -fno-strict-aliasing)

# Evidence harness (replays the Lean-generated vectors; see validation/native/smc_harness.cpp): ./smc_harness --vectors <vectors.txt>, --text
add_executable(smc_harness validation/native/smc_harness.cpp "${TP_GAS}")
target_include_directories(smc_harness PRIVATE "${CMAKE_SOURCE_DIR}/SelfModTamper")
target_compile_options(smc_harness PRIVATE -fno-strict-aliasing)
if(asmjit_FOUND)
    target_link_libraries(smc_harness PRIVATE asmjit::asmjit)
    target_compile_definitions(smc_harness PRIVATE SMC_WITH_ASMJIT)
endif()
