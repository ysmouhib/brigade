# Experiment log

Smoke set `scripts/bench_problems.jsonl` (5 easy and 3 medium true claims, 3 false), DeepSeek
`deepseek-flash`, Lean v4.35.0 REPL, budgets rounds 1 / repair 2 / depth 1 / 1 brainstormer,
one run per version unless noted. Newest first.

| Run | Date | Server code | Change tested | As expected | True proved | False refuted | Wrong | Time (s) | LLM calls | Lean calls |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| R3 | 2026-10-20 | `0497156` | Proof indentation kept; quick attempt before planning; cancellation fix | pending | | | | | | |
| R2 | 2026-10-20 | `1be5ae8` | Cascade branches must close the goal; only the winning tactic kept | 7/11 | 4/8 | 3/3 | 0 | 1461 | 128 | 100 |
| R1 | 2026-10-20 | `a5fbe50` | Baseline | 6/11 | 3/8 (1 cancelled by hand) | 3/3 | 0 | 1709 | 144 | 107 |

## Findings

- R1: 15 of 19 multi-line proof attempts reached Lean with broken indentation (reply cleaning
  stripped only the first line); easy claims paid for a full plan (`succ_le_double`: 8 LLM calls
  for a goal `omega` closes). Fixed in R3.
- R2: the new cascade works in real Lean (`positivity`, `omega`, `ring`, `nlinarith` recorded as
  winners). `even_sq_plus_self` missed because a correct first proof was dropped unchecked when it
  was the only candidate left in a strategic batch. Fixed in `d178eab` (after R3).
