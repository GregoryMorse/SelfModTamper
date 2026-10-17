<#
.SYNOPSIS
    Downloads the digitally signed WinRing0 1.2.0 x64 kernel driver and places
    WinRing0x64.sys in the repository root so CMake copies it to the build output.

.DESCRIPTION
    The WinRing0 driver is required for privileged MSR access (reading/writing
    IA32_PERFEVTSEL0 and IA32_PMC0 to count MACHINE_CLEARS.SMC events).
    Without it the benchmark still runs but all MACHINE_CLEARS.SMC counters
    will read zero.

    Run once before your first cmake configuration:

        powershell -ExecutionPolicy Bypass -File scripts\Get-WinRing0.ps1

    Then re-run cmake so it picks up the newly placed file:

        cmake --preset windows-x64

.PARAMETER DestinationDir
    Directory in which to place WinRing0x64.sys.
    Defaults to the repository root (the parent of the 'scripts' folder).
#>
param(
    [string]$DestinationDir = (Split-Path -Parent $PSScriptRoot)
)

$ErrorActionPreference = 'Stop'

$dest = Join-Path $DestinationDir 'WinRing0x64.sys'

if (Test-Path $dest) {
    Write-Host "WinRing0x64.sys already present at '$dest' - nothing to do." `
        -ForegroundColor Green
    exit 0
}

# Primary source: official OpenLibSys WinRing0 1.2.0 distribution.
# If this URL becomes unavailable, the same signed driver is bundled in many
# open-source hardware-monitoring projects (e.g. LibreHardwareMonitor).
$zipUrl  = 'http://openlibsys.org/dl/WinRing0-1.2.0.zip'
$zipPath = Join-Path $env:TEMP 'WinRing0.zip'
$extract = Join-Path $env:TEMP 'WinRing0Extract'

Write-Host "Downloading WinRing0 from $zipUrl ..." -ForegroundColor Cyan
try {
    Invoke-WebRequest -Uri $zipUrl -OutFile $zipPath -UseBasicParsing
}
catch {
    Write-Error (
        "Download failed: $_`n" +
        "Please download WinRing0_1_2_0.zip manually from http://openlibsys.org/ " +
        "and copy WinRing0x64.sys to: $DestinationDir"
    )
}

Write-Host "Extracting ..."
if (Test-Path $extract) { Remove-Item $extract -Recurse -Force }
Expand-Archive -Path $zipPath -DestinationPath $extract -Force

$found = Get-ChildItem -Path $extract -Filter 'WinRing0x64.sys' -Recurse |
         Select-Object -First 1

if (-not $found) {
    Write-Error (
        "WinRing0x64.sys was not found inside the downloaded archive.`n" +
        "Please download WinRing0_1_2_0.zip manually from http://openlibsys.org/ " +
        "and copy WinRing0x64.sys to: $DestinationDir"
    )
}

Copy-Item -Path $found.FullName -Destination $dest -Force
Write-Host "Placed WinRing0x64.sys at: $dest" -ForegroundColor Green
Write-Host "Now re-run cmake so it picks up the driver:" -ForegroundColor Yellow
Write-Host "    cmake --preset windows-x64" -ForegroundColor Yellow

Remove-Item $zipPath -Force -ErrorAction SilentlyContinue
Remove-Item $extract -Recurse -Force -ErrorAction SilentlyContinue
