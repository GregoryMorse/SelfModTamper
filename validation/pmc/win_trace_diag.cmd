@echo off
rem Diagnostic for the Windows/Intel counter: does Windows record MACHINE_CLEARS.SMC (source registered by
rem   python validation\pmc_test.py --register-wpr) in a kernel trace at all?  Run from an ADMINISTRATOR prompt in the repo root.
rem   validation\pmc\win_trace_diag.cmd
rem Writes validation\native\pmc\trace_diag\{diag.etl,dumper.txt,pmc.txt,probe.txt}; send those files (or the folder) to the author.
setlocal
cd /d "%~dp0\..\.."
set XP="C:\Program Files (x86)\Windows Kits\10\Windows Performance Toolkit\xperf.exe"
set OUT=validation\native\pmc\trace_diag
if not exist %OUT% mkdir %OUT%
if not exist validation\.build\pmc\Release\smc_pmc_probe.exe (
  echo build the probe first: python validation\pmc_test.py
  exit /b 1
)
%XP% -stop > nul 2>&1
%XP% -stop -d > nul 2>&1
echo starting the trace
%XP% -on PROC_THREAD+LOADER -Pmc MACHINE_CLEARS.SMC CSWITCH strict -f %OUT%\kernel.etl
if errorlevel 1 (echo xperf -on failed & exit /b 1)
validation\.build\pmc\Release\smc_pmc_probe.exe --iters 200000 --reps 5 > %OUT%\probe.txt 2>&1
echo stopping the trace
%XP% -d %OUT%\diag.etl
%XP% -i %OUT%\diag.etl -o %OUT%\dumper.txt -a dumper > nul 2>&1
%XP% -i %OUT%\diag.etl -o %OUT%\pmc.txt -a pmc > nul 2>&1
dir %OUT%
echo done: send the folder %OUT%
