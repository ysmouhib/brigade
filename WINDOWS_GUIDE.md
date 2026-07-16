# Brigade on Windows

The server is plain Python and the client is your browser, so Windows works out of
the box for the offline demo and for real Claude runs. The only component with a
platform story is the Lean verifier (see below).

## Prerequisites

- Python 3.10+ on PATH (`python --version`)
- PowerShell (any recent Windows has it)

## One-shot demo (no API key, no Lean)

From the repository root:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\windows_demo.ps1
```

This creates `.venv`, installs the server, runs the test suite (should say
`39 passed`), and starts the server. Open http://localhost:8811 and pick the
"Scripted replay" engine in the New Problem form.

## Running the server day-to-day

```powershell
.\scripts\run_server.ps1 -Demo    # offline demo engine, no key needed
.\scripts\run_server.ps1          # real mode; reads .env (see .env.example)
```

`run_server.ps1` loads `.env` from the repository root, so `copy .env.example .env`
and put your `ANTHROPIC_API_KEY` in it — or just paste the key in the web UI's
Settings panel after starting.

## The Lean verifier on Windows

`scripts/setup_lean.sh` is a bash script. Two supported routes:

1. **WSL (recommended):** run `bash scripts/setup_lean.sh` inside WSL, run the
   server there too, and use any Windows browser as the client. This is the
   least-friction way to get `LEAN_MODE=file` or `LEAN_MODE=repl` working.
2. **Native:** Lean 4 and elan do support Windows. Install elan from
   https://leanprover.github.io/ and replicate the script's steps by hand (pinned
   `lean-toolchain`, `lakefile.lean` requiring mathlib at the same tag,
   `lake update mathlib && lake exe cache get && lake build`), then point
   `LEAN_PROJECT_DIR` at the project. This route is not exercised by the scripts in
   this repository, so expect to troubleshoot.

Everything else — the web UI, budgets, strategic verification, the API — is
identical to the Linux/macOS instructions in [README.md](README.md).
