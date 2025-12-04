@echo off
REM Get the directory of this script
set SCRIPT_DIR=%~dp0

REM Go to the parent folder
for %%I in ("%SCRIPT_DIR%..") do set PARENT_DIR=%%~fI

echo ## update >> "%PARENT_DIR%\_quarto.yml"