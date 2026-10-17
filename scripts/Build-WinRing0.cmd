@echo off
rem Builds WinRing0x64.sys from source (pinned commit of github.com/GermanAizek/WinRing0) with CMake, the MSVC tools and Microsoft's WDK NuGet package.
rem No installer and no administrator rights are needed.  Extra arguments go to cmake, e.g.  scripts\Build-WinRing0.cmd -DWINRING0_TESTSIGN=ON
cd /d "%~dp0.."
cmake -S cmake\winring0 -B build\winring0 %*
