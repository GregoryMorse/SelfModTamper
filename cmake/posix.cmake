# Linux (x86-64) build of SelfModTamper: the MASM kernels in TP.asm are translated to GNU as by scripts/masm2gas.py (no extra
# assembler to install), the Windows API is replaced by SelfModTamper/platform_posix.h and the WinRing0 driver by perf_event_open.
# asmjit is fetched by CMake from a pinned, hash-checked archive (cmake/asmjit.cmake); -DSMC_WITH_ASMJIT=OFF skips the dynamic variant.
option(SMC_WITH_ASMJIT "Build the dynamic (asmjit) variant" ON)
if(NOT CMAKE_SYSTEM_NAME MATCHES "Linux|Darwin" OR NOT CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64|AMD64")
    message(FATAL_ERROR "The POSIX build of SelfModTamper supports Linux and macOS on x86-64 only.")
endif()
set(TP_GAS_ARGS "")
if(APPLE)
    set(TP_GAS_ARGS --macho)  # Mach-O symbol names carry a leading underscore; no .type/.size
endif()
enable_language(ASM)
find_package(Python3 REQUIRED COMPONENTS Interpreter)
set(TP_GAS "${CMAKE_CURRENT_BINARY_DIR}/TP.gas.S")
add_custom_command(OUTPUT "${TP_GAS}"
    COMMAND Python3::Interpreter "${CMAKE_SOURCE_DIR}/scripts/masm2gas.py" "${CMAKE_SOURCE_DIR}/SelfModTamper/TP.asm" "${TP_GAS}" ${TP_GAS_ARGS}
    DEPENDS "${CMAKE_SOURCE_DIR}/SelfModTamper/TP.asm" "${CMAKE_SOURCE_DIR}/scripts/masm2gas.py"
    COMMENT "Translating TP.asm (MASM) to GNU as")
add_executable(SelfModTamper SelfModTamper/SelfModTamper.cpp "${TP_GAS}")
if(SMC_WITH_ASMJIT)
    include(${CMAKE_CURRENT_LIST_DIR}/asmjit.cmake)
    target_link_libraries(SelfModTamper PRIVATE asmjit::asmjit)
    target_compile_definitions(SelfModTamper PRIVATE SMC_WITH_ASMJIT)
endif()
target_compile_options(SelfModTamper PRIVATE -fno-strict-aliasing)
if(APPLE)
    # the kernels modify their own code: give the __TEXT segment rwx protection (x86-64 macOS, no hardened runtime)
    target_link_options(SelfModTamper PRIVATE -Wl,-segprot,__TEXT,rwx,rwx)
endif()

# Evidence harness (replays the Lean-generated vectors; see validation/native/smc_harness.cpp): ./smc_harness --vectors <vectors.txt>, --text
add_executable(smc_harness validation/native/smc_harness.cpp "${TP_GAS}")
target_include_directories(smc_harness PRIVATE "${CMAKE_SOURCE_DIR}/SelfModTamper")
target_compile_options(smc_harness PRIVATE -fno-strict-aliasing)
if(APPLE)
    target_link_options(smc_harness PRIVATE -Wl,-segprot,__TEXT,rwx,rwx)
endif()
if(SMC_WITH_ASMJIT)
    target_link_libraries(smc_harness PRIVATE asmjit::asmjit)
    target_compile_definitions(smc_harness PRIVATE SMC_WITH_ASMJIT)
endif()
