# Brigade: working notes for Claude Code

Brigade is a multi-agent theorem prover: LLM agents plan, formalize and prove a claim in
Lean 4 + Mathlib, and a result counts only when Lean accepts it. See README.md for the design.

## This machine (WSL Ubuntu)

- Repo: `~/projects/brigade`, branch `phase-0-fixes`. Python venv: `source .venv/bin/activate`.
- Lean v4.35.0 + Mathlib in `lean/BrigadeLean`, REPL in `lean/repl` (built by `scripts/setup_lean.sh`).
- `.env` holds the model key (`LLM_PROVIDER=openai`, DeepSeek `deepseek-flash`, `LEAN_MODE=repl`).
  Never print, copy or commit `.env`.

## Running

- Server: `bash scripts/run_server.sh`, then wait for `<- Lean REPL: ready in …s`. Loading Mathlib
  takes about 8 minutes here, so keep the server running between experiments and restart it only
  when server code changed. Check it with `curl -s localhost:8811/health` (`lean_ready`,
  `server_git` = the commit the server loaded).
- Tests: `cd server && python -m pytest -q`. The Lean fixture tests run here (real Lean output is
  recorded under `server/tests/fixtures/lean/`); everything should pass.
- Benchmark: `python3 scripts/bench.py` (needs the server). Writes
  `experiments/results/<date>-<time>-<set>/`: `summary.md`, `results.csv`, and `jobs/<name>.json`
  with every event of every job. Outcomes: `ok`, `miss` (no verdict), `WRONG` (opposite verdict:
  stop and investigate).

## The experiment loop

1. Run the bench on the current code (one change per run, so the effect is attributable).
2. Record the run in `experiments/LOG.md` (newest first).
3. Diagnose every miss from `jobs/<name>.json`: read the `prove_attempt` and `lean_check` events.
   Most failures so far were bugs in Brigade, not in the model's mathematics.
4. Fix with a failing test first, built from the real failure in the trace.
5. Restart the server (new code) and run the bench again.

One run per version cannot separate a one-problem difference from model variance; repeat runs
before concluding a small change helped.

## Rules

- Never weaken acceptance: VERIFIED means Lean compiled the exact pinned statement with no errors
  and no `sorry`; the axiom audit fails closed. Every change keeps that.
- Do not cancel jobs (browser or otherwise) while a benchmark runs; it skews timings.
- Do not push to GitHub without the user's explicit go-ahead: the repo is public, and pushing to
  `main` redeploys the public website. Work on `phase-0-fixes`.
- Commit messages explain why, citing the trace evidence that motivated the change.

## Known issues / next candidates

- Library names drift between Mathlib versions (`abs_add` no longer exists): candidates for
  Lean's own library search (`exact?`) in the cascade, keeping the lemma it finds.
- A REPL timeout restarts the REPL, which reloads Mathlib (about 8 minutes on this machine).
- The prover occasionally returns no parseable JSON (seen once on `sqrt2_irrational`).
- `bench.py` has no repeat option yet.
