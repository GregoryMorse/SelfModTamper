# Builds the WinRing0 kernel driver (WinRing0x64.sys) from source, with no manual setup and no administrator rights:
#
#   scripts\Build-WinRing0.cmd          (or: cmake -S cmake/winring0 -B build/winring0)
#
#  * source: the pinned commit of the open-source repository https://github.com/GermanAizek/WinRing0 (a git clone, not a binary);
#  * headers and import libraries: Microsoft's Windows Driver Kit NuGet package Microsoft.Windows.WDK.x64 (pinned version, SHA-256 checked,
#    only the kernel-mode headers and x64 libraries are extracted), so the WDK installer is not needed;
#  * compiler and linker: the MSVC tools of the installed Visual Studio / Build Tools (found with vswhere).
# The driver is plain WDM (ntddk.h), so cl + link suffice.  Output: <repo>/build/winring0/WinRing0x64.sys (override with -DWINRING0_OUT=...).
#
# The result is UNSIGNED.  Windows loads a kernel driver only if it is signed:  -DWINRING0_TESTSIGN=ON signs it with a self-made
# certificate (signtool from the Windows SDK), which Windows then accepts only in test-signing mode (`bcdedit /set testsigning on`,
# needs Secure Boot and Memory integrity off).  This script never changes boot or security settings.
cmake_minimum_required(VERSION 3.24)
project(WinRing0Driver NONE)

set(WINRING0_REPO   "https://github.com/GermanAizek/WinRing0.git" CACHE STRING "Source repository")
set(WINRING0_COMMIT "d56744051099a0382ff1bd18de15c6b13b98a079" CACHE STRING "Pinned commit (update deliberately, never track a branch)")
set(WDK_NUPKG_VERSION "10.0.26100.6584")
set(WDK_NUPKG_SHA256  "c393d03dfb640b5c92f546b32f6770ef68cd3aaf691956e7d66d8e2c28a1b55e")
set(WDK_INC_VERSION   "10.0.26100.0")   # directory name inside the package
get_filename_component(_repo_root "${CMAKE_CURRENT_LIST_DIR}/../.." ABSOLUTE)
set(WINRING0_OUT "${_repo_root}/build/winring0" CACHE PATH "Directory that receives WinRing0x64.sys")
option(WINRING0_TESTSIGN "Test-sign the driver with a generated self-signed certificate" OFF)

set(_work "${CMAKE_BINARY_DIR}")
set(_src  "${_work}/src")
set(_wdk  "${_work}/wdk")
set(_out  "${_work}/out")

# 1. source at the pinned commit
find_package(Git REQUIRED)
if(NOT EXISTS "${_src}/.git")
  execute_process(COMMAND "${GIT_EXECUTABLE}" clone --quiet "${WINRING0_REPO}" "${_src}" RESULT_VARIABLE _r)
  if(_r)
    message(FATAL_ERROR "git clone ${WINRING0_REPO} failed (${_r})")
  endif()
endif()
execute_process(COMMAND "${GIT_EXECUTABLE}" -C "${_src}" checkout --quiet "${WINRING0_COMMIT}" RESULT_VARIABLE _r)
if(_r)
  message(FATAL_ERROR "git checkout ${WINRING0_COMMIT} failed (${_r})")
endif()
message(STATUS "WinRing0 source at ${WINRING0_COMMIT}")

# 2. kernel-mode headers and libraries from the WDK NuGet package
if(NOT EXISTS "${_wdk}/c/Lib/${WDK_INC_VERSION}/km/x64/ntoskrnl.lib")
  set(_pkg "${_work}/wdk.nupkg")
  message(STATUS "Downloading Microsoft.Windows.WDK.x64 ${WDK_NUPKG_VERSION} (about 110 MB) ...")
  file(DOWNLOAD "https://api.nuget.org/v3-flatcontainer/microsoft.windows.wdk.x64/${WDK_NUPKG_VERSION}/microsoft.windows.wdk.x64.${WDK_NUPKG_VERSION}.nupkg"
       "${_pkg}" EXPECTED_HASH SHA256=${WDK_NUPKG_SHA256} SHOW_PROGRESS STATUS _st)
  list(GET _st 0 _code)
  if(_code)
    message(FATAL_ERROR "WDK package download failed: ${_st}")
  endif()
  file(ARCHIVE_EXTRACT INPUT "${_pkg}" DESTINATION "${_wdk}"
       PATTERNS "c/Include/${WDK_INC_VERSION}/km/*" "c/Include/${WDK_INC_VERSION}/shared/*" "c/Lib/${WDK_INC_VERSION}/km/x64/*")
  file(REMOVE "${_pkg}")
endif()
set(_kc "${_wdk}/c")
if(NOT EXISTS "${_kc}/Include/${WDK_INC_VERSION}/km/ntddk.h")
  message(FATAL_ERROR "ntddk.h missing after extracting the WDK package")
endif()

# 3. MSVC tools
find_program(_vswhere vswhere HINTS "$ENV{ProgramFiles\(x86\)}/Microsoft Visual Studio/Installer")
if(NOT _vswhere)
  message(FATAL_ERROR "vswhere.exe not found: install Visual Studio or the Build Tools with the C++ workload.")
endif()
execute_process(COMMAND "${_vswhere}" -latest -prerelease -products * -requires Microsoft.VisualStudio.Component.VC.Tools.x86.x64
                        -find VC/Auxiliary/Build/vcvars64.bat OUTPUT_VARIABLE _vcvars OUTPUT_STRIP_TRAILING_WHITESPACE)
string(REGEX REPLACE "\r?\n.*" "" _vcvars "${_vcvars}")
if(NOT _vcvars)
  message(FATAL_ERROR "The MSVC x64 tools were not found through vswhere (install the 'Desktop development with C++' workload).")
endif()
message(STATUS "MSVC environment: ${_vcvars}")

# 4. compile and link (a generated batch file, so the Visual Studio environment applies; forward slashes are fine for cl and link)
string(REPLACE "/" "\\" _vcvars_n "${_vcvars}")
file(MAKE_DIRECTORY "${_out}")
set(_i "${_kc}/Include/${WDK_INC_VERSION}")
file(WRITE "${_work}/build_driver.bat"
"@echo off
call \"${_vcvars_n}\" >nul || exit /b 1
cl /nologo /c /kernel /GS- /Gz /W3 /O2 /Zl /D_AMD64_ /DAMD64 /D_WIN64 /D_WIN32_WINNT=0x0A00 /DWINVER=0x0A00 /DNTDDI_VERSION=0x0A000010 /DPOOL_NX_OPTIN=1 /DNDEBUG /I\"${_i}/km\" /I\"${_i}/km/crt\" /I\"${_i}/shared\" /Fo\"${_out}/OpenLibSys.obj\" \"${_src}/WinRing0Sys/OpenLibSys.c\" || exit /b 1
link /nologo /DRIVER /SUBSYSTEM:NATIVE /ENTRY:DriverEntry /NODEFAULTLIB /RELEASE /INTEGRITYCHECK /MERGE:_TEXT=.text /OUT:\"${_out}/WinRing0x64.sys\" \"${_out}/OpenLibSys.obj\" /LIBPATH:\"${_kc}/Lib/${WDK_INC_VERSION}/km/x64\" ntoskrnl.lib hal.lib wdmsec.lib BufferOverflowFastFailK.lib ntstrsafe.lib || exit /b 1
")
execute_process(COMMAND cmd /c "${_work}/build_driver.bat" RESULT_VARIABLE _r)
if(_r OR NOT EXISTS "${_out}/WinRing0x64.sys")
  message(FATAL_ERROR "Compiling or linking the driver failed (${_r}).")
endif()

# 5. optional test signing
if(WINRING0_TESTSIGN)
  file(GLOB _st_candidates "$ENV{ProgramFiles\(x86\)}/Windows Kits/10/bin/*/x64/signtool.exe")
  list(SORT _st_candidates)
  list(POP_BACK _st_candidates _signtool)
  if(NOT _signtool)
    message(FATAL_ERROR "signtool.exe not found (Windows SDK).")
  endif()
  file(WRITE "${_work}/testsign.ps1"
"$c = New-SelfSignedCertificate -Type CodeSigningCert -Subject 'CN=WinRing0 test signing' -CertStoreLocation Cert:/CurrentUser/My
& '${_signtool}' sign /fd sha256 /sha1 $c.Thumbprint '${_out}/WinRing0x64.sys'
exit $LASTEXITCODE
")
  execute_process(COMMAND powershell -NoProfile -ExecutionPolicy Bypass -File "${_work}/testsign.ps1" RESULT_VARIABLE _r)
  if(_r)
    message(FATAL_ERROR "Test signing failed (${_r}).")
  endif()
endif()

file(MAKE_DIRECTORY "${WINRING0_OUT}")
file(COPY "${_out}/WinRing0x64.sys" DESTINATION "${WINRING0_OUT}")
file(SHA256 "${WINRING0_OUT}/WinRing0x64.sys" _h)
message(STATUS "Built ${WINRING0_OUT}/WinRing0x64.sys  sha256=${_h}  (unsigned unless -DWINRING0_TESTSIGN=ON)")
