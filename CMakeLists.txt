cmake_minimum_required(VERSION 3.21)
project(SelfModTamper CXX ASM_MASM)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# ── x64-only guard ────────────────────────────────────────────────────────────
if(NOT CMAKE_SIZEOF_VOID_P EQUAL 8)
    message(FATAL_ERROR "SelfModTamper requires a 64-bit (x64) build.")
endif()

# ── Dependencies (resolved by vcpkg) ─────────────────────────────────────────
find_package(asmjit CONFIG REQUIRED)

# ── Target ────────────────────────────────────────────────────────────────────
add_executable(SelfModTamper
    SelfModTamper/SelfModTamper.cpp
    SelfModTamper/TP.asm
)

target_link_libraries(SelfModTamper PRIVATE
    asmjit::asmjit
    psapi       # EnumProcessModules, GetModuleInformation
    winmm       # timeBeginPeriod, timeGetTime, timeEndPeriod
)

# The .text section must be read-write-execute for the static SMC variants.
target_link_options(SelfModTamper PRIVATE "/SECTION:.text,RWE")

# ── Runtime DLLs ──────────────────────────────────────────────────────────────
# Copies asmjit.dll (and any other vcpkg runtime DLLs) next to the executable.
add_custom_command(TARGET SelfModTamper POST_BUILD
    COMMAND ${CMAKE_COMMAND} -E copy_if_different
        $<TARGET_RUNTIME_DLLS:SelfModTamper>
        $<TARGET_FILE_DIR:SelfModTamper>
    COMMAND_EXPAND_LISTS
    COMMENT "Copying runtime DLLs"
)

# ── WinRing0 driver (optional) ────────────────────────────────────────────────
# Place WinRing0x64.sys in the repository root (run scripts/Get-WinRing0.ps1)
# before running cmake; it will then be copied next to the executable.
if(EXISTS "${CMAKE_SOURCE_DIR}/WinRing0x64.sys")
    add_custom_command(TARGET SelfModTamper POST_BUILD
        COMMAND ${CMAKE_COMMAND} -E copy_if_different
            "${CMAKE_SOURCE_DIR}/WinRing0x64.sys"
            "$<TARGET_FILE_DIR:SelfModTamper>/WinRing0x64.sys"
        COMMENT "Copying WinRing0x64.sys"
    )
else()
    message(STATUS
        "WinRing0x64.sys not found in repository root. "
        "Run  scripts/Get-WinRing0.ps1  and re-run cmake to enable "
        "MACHINE_CLEARS.SMC performance-counter features.")
endif()
