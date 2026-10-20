# Start the Brigade server on Windows (PowerShell).
# Usage:  .\scripts\run_server.ps1           (real mode, needs key in .env or UI)
#         .\scripts\run_server.ps1 -Demo     (offline demo engine, no key needed)
param([switch]$Demo)
$ErrorActionPreference = "Stop"
. "$PSScriptRoot\load_env.ps1"
Set-Location "$PSScriptRoot\..\server"
if (Test-Path "..\.env") { Import-DotEnv "..\.env" }
if ($Demo) { $env:FAKE_LLM = "1"; $env:LEAN_MODE = "fake" }
python -m uvicorn app.main:app --host 0.0.0.0 --port 8811 --no-access-log
