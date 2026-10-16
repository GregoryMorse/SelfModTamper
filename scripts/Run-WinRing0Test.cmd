@echo off
rem Runs the WinRing0 test of the benchmark product (before and after the fixes) and saves everything under
rem validation\native\winring0\<timestamp>\ . It asks for administrator rights itself.
cd /d "%~dp0.."
python validation\winring0_test.py %*
