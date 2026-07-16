# Start the Brigade server on Windows (PowerShell).
# Usage:  .\scripts\run_server.ps1           (real mode, needs key in .env or UI)
#         .\scripts\run_server.ps1 -Demo     (offline demo engine, no key needed)
param([switch]$Demo)
$ErrorActionPreference = "Stop"
Set-Location "$PSScriptRoot\..\server"
if ($Demo) { $env:FAKE_LLM = "1"; $env:LEAN_MODE = "fake" }
if (Test-Path "..\.env") {
  Get-Content "..\.env" | Where-Object { $_ -match "^\s*[^#].*=" } | ForEach-Object {
    $k, $v = $_ -split "=", 2
    [Environment]::SetEnvironmentVariable($k.Trim(), $v.Trim(), "Process")
  }
}
python -m uvicorn app.main:app --host 0.0.0.0 --port 8811
