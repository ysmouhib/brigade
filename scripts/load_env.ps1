# Load a .env file into the current PowerShell process, the way dotenv files are written:
# whole-line comments are skipped, an inline "# comment" after whitespace is dropped,
# and surrounding quotes are removed ("abc#def" keeps its '#').
# Usage:  . .\scripts\load_env.ps1; Import-DotEnv ".env"
function Import-DotEnv([string]$Path) {
  foreach ($line in Get-Content -LiteralPath $Path) {
    if ($line -notmatch '^\s*([^#=\s][^=]*?)\s*=(.*)$') { continue }
    $key = $Matches[1].Trim()
    $value = $Matches[2].Trim()
    if ($value -match '^"(.*)"(\s+#.*)?$' -or $value -match "^'(.*)'(\s+#.*)?$") {
      $value = $Matches[1]
    } else {
      $value = ($value -replace '(^|\s+)#.*$', '').Trim()
    }
    [Environment]::SetEnvironmentVariable($key, $value, "Process")
  }
}
