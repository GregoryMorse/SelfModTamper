# Builds the WinRing0 kernel driver (WinRing0x64.sys) from source: a pinned commit of the open-source repository
# https://github.com/GermanAizek/WinRing0 (GPL-3.0), compiled with the Windows Driver Kit through MSBuild.
# Nothing is downloaded as a binary.  The result is an UNSIGNED driver (see below).
#
#   cmake -S cmake/winring0 -B build/winring0
#   cmake --build build/winring0
#
# Needs: Visual Studio (or Build Tools) with the C++ workload and the matching Windows Driver Kit (WDK) -
# "Windows Driver Kit" from https://learn.microsoft.com/windows-hardware/drivers/download-the-wdk , plus its VS extension.
# Output: <repo>/WinRing0x64.sys (override with -DWINRING0_OUT=...).
#
# Signing: Windows loads a kernel driver only if it is signed.  This build does not sign.  Options on a test machine:
#   -DWINRING0_TESTSIGN=ON   signs with a self-made test certificate (needs signtool from the WDK/SDK); Windows then loads it only in
#                            test-signing mode (`bcdedit /set testsigning on`, which needs Secure Boot off and Memory integrity off).
# This script never changes boot or security settings.
cmake_minimum_required(VERSION 3.24)
project(WinRing0Driver NONE)

set(WINRING0_REPO   "https://github.com/GermanAizek/WinRing0.git" CACHE STRING "Source repository")
# Pinned commit (master of 2024-01-17); update deliberately, never track a branch.
set(WINRING0_COMMIT "d56744051099a0382ff1bd18de15c6b13b98a079" CACHE STRING "Pinned commit")
get_filename_component(_repo_root "${CMAKE_CURRENT_LIST_DIR}/../.." ABSOLUTE)
set(WINRING0_OUT "${_repo_root}" CACHE PATH "Directory that receives WinRing0x64.sys")
option(WINRING0_TESTSIGN "Test-sign the driver with a generated self-signed certificate" OFF)

# MSBuild through vswhere
find_program(_vswhere vswhere HINTS "$ENV{ProgramFiles\(x86\)}/Microsoft Visual Studio/Installer")
if(NOT _vswhere)
  message(FATAL_ERROR "vswhere.exe not found: install Visual Studio or the Build Tools.")
endif()
execute_process(COMMAND "${_vswhere}" -latest -prerelease -products * -requires Microsoft.Component.MSBuild
                        -find MSBuild/**/Bin/MSBuild.exe OUTPUT_VARIABLE _msbuild OUTPUT_STRIP_TRAILING_WHITESPACE)
string(REGEX REPLACE "\n.*" "" _msbuild "${_msbuild}")
if(NOT _msbuild)
  message(FATAL_ERROR "MSBuild not found through vswhere.")
endif()

# Windows Driver Kit: the newest kit version that has kernel-mode headers
file(GLOB _km "$ENV{ProgramFiles\(x86\)}/Windows Kits/10/Include/*/km/wdm.h")
if(NOT _km)
  message(FATAL_ERROR "The Windows Driver Kit is not installed (no Windows Kits/10/Include/<ver>/km/wdm.h).\n"
          "Install the WDK that matches your Windows SDK and its Visual Studio extension, then re-run.")
endif()
list(SORT _km)
list(POP_BACK _km _wdm)
get_filename_component(_d "${_wdm}" DIRECTORY)
get_filename_component(_d "${_d}" DIRECTORY)
get_filename_component(WDK_VERSION "${_d}" NAME)
message(STATUS "MSBuild: ${_msbuild}")
message(STATUS "WDK/SDK version: ${WDK_VERSION}")

include(ExternalProject)
set(_src "${CMAKE_BINARY_DIR}/src")
set(_obj "${CMAKE_BINARY_DIR}/out")
ExternalProject_Add(winring0_src
  GIT_REPOSITORY "${WINRING0_REPO}"
  GIT_TAG        "${WINRING0_COMMIT}"
  GIT_SHALLOW    OFF
  SOURCE_DIR     "${_src}"
  CONFIGURE_COMMAND ""
  BUILD_IN_SOURCE 1
  BUILD_COMMAND  "${_msbuild}" "${_src}/WinRing0Sys/WinRing0Sys.vcxproj" /nologo /m
                 /p:Configuration=Release /p:Platform=x64 /p:SignMode=Off
                 /p:WindowsTargetPlatformVersion=${WDK_VERSION} "/p:OutDir=${_obj}/"
  INSTALL_COMMAND ""
  USES_TERMINAL_BUILD ON)

ExternalProject_Add_Step(winring0_src stage
  COMMAND ${CMAKE_COMMAND} -E make_directory "${WINRING0_OUT}"
  COMMAND ${CMAKE_COMMAND} -E copy "${_obj}/WinRing0x64.sys" "${WINRING0_OUT}/WinRing0x64.sys"
  COMMAND ${CMAKE_COMMAND} -E sha256sum "${WINRING0_OUT}/WinRing0x64.sys"
  DEPENDEES build)

if(WINRING0_TESTSIGN)
  find_program(_signtool signtool HINTS "$ENV{ProgramFiles\(x86\)}/Windows Kits/10/bin/${WDK_VERSION}/x64")
  if(NOT _signtool)
    message(FATAL_ERROR "signtool.exe not found (WDK/SDK).")
  endif()
  ExternalProject_Add_Step(winring0_src testsign
    COMMAND powershell -NoProfile -Command
      "$c = New-SelfSignedCertificate -Type CodeSigningCert -Subject 'CN=WinRing0 test signing' -CertStoreLocation Cert:\CurrentUser\My; & '${_signtool}' sign /fd sha256 /sha1 $c.Thumbprint '${WINRING0_OUT}/WinRing0x64.sys'"
    DEPENDEES stage)
endif()
