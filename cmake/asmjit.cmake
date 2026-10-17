# asmjit, fetched and built by CMake from a pinned source archive (no vcpkg needed).  The commit and the SHA-512 are the ones the
# vcpkg baseline of this repository uses for its asmjit port (library version 1.14.0), so the dynamic kernel is the same code.
include(FetchContent)
set(ASMJIT_STATIC ON CACHE BOOL "" FORCE)
set(ASMJIT_TEST OFF CACHE BOOL "" FORCE)
set(ASMJIT_NO_INSTALL ON CACHE BOOL "" FORCE)
FetchContent_Declare(asmjit
    URL https://github.com/asmjit/asmjit/archive/9eb6edbf711ceb25346ee40bae68b40a4505cdf5.tar.gz
    URL_HASH SHA512=9c3567634205bf0c64462833b28b6bbf1c1965216aa09872196048953417fab18822d94d70d112f7a506396a5b94716d714316dd2559c3509edf1273650768b9
    DOWNLOAD_EXTRACT_TIMESTAMP TRUE)
FetchContent_MakeAvailable(asmjit)
if(NOT TARGET asmjit::asmjit)
    add_library(asmjit::asmjit ALIAS asmjit)
endif()
