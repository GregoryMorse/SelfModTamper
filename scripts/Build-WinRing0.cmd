@echo off
rem Builds WinRing0x64.sys from source (pinned commit of github.com/GermanAizek/WinRing0) with CMake, MSBuild and the Windows Driver Kit.
rem Extra arguments go to the configure step, e.g.  scripts\Build-WinRing0.cmd -DWINRING0_TESTSIGN=ON
cd /d "%~dp0.."
cmake -S cmake\winring0 -B build\winring0 %* || exit /b 1
cmake --build build\winring0
