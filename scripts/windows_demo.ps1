# One-shot Windows setup + demo launch. Run from the brigade folder:
#   powershell -ExecutionPolicy Bypass -File scripts\windows_demo.ps1
$ErrorActionPreference = "Stop"
Set-Location "$PSScriptRoot\.."
Write-Host "== Brigade: Windows demo setup ==" -ForegroundColor Yellow
python --version
if (-not (Test-Path ".venv")) { python -m venv .venv }
& .\.venv\Scripts\pip.exe install --quiet -e server/ pytest pytest-asyncio
Write-Host "-- running the test suite (should say '39 passed')" -ForegroundColor Yellow
Push-Location server
& ..\.venv\Scripts\python.exe -m pytest -q
Pop-Location
Write-Host "-- starting the server. Open  http://localhost:8811  in your browser." -ForegroundColor Green
Write-Host "   (Press Ctrl+C here to stop it.)"
$env:FAKE_LLM = "0"   # real mode; the UI offers the offline demo engine per job
Set-Location server
& ..\.venv\Scripts\python.exe -m uvicorn app.main:app --port 8811
