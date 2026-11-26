<#
.SYNOPSIS
    Optional helper to add Mathlib to lakefile.toml and fetch precompiled olean caches.
    Requires network access and ~5-10 GB disk space.
#>
param(
    [string]$MathlibRev = "v4.35.0"
)

$ErrorActionPreference = "Stop"
$RepoRoot = Split-Path -Parent $PSScriptRoot
$Lakefile = Join-Path $RepoRoot "lakefile.toml"

if (-not (Test-Path $Lakefile)) {
    throw "lakefile.toml not found at $Lakefile"
}

$content = Get-Content $Lakefile -Raw
if ($content -match "name = ""mathlib""") {
    Write-Host "Mathlib dependency already present in lakefile.toml"
} else {
    $addition = @"

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "$MathlibRev"
"@
    Add-Content -Path $Lakefile -Value $addition -Encoding UTF8
    Write-Host "Added mathlib ($MathlibRev) to lakefile.toml"
}

Push-Location $RepoRoot
try {
    lake update mathlib
    lake exe cache get
    lake build
} finally {
    Pop-Location
}
