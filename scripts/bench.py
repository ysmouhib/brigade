#!/usr/bin/env python3
"""Benchmark harness: run a JSONL problem set through the real pipeline and report.

Usage (needs a Lean install and an API key — see README Quickstart 2):
    python3 scripts/bench.py [problems.jsonl]           # defaults to bench_problems.jsonl
    python3 scripts/bench.py --dry-run                  # validate the file only

Each line: {"name": str, "problem": str, "expect": "proved"|"refuted"|null}
The report counts proved / refuted / exhausted / error and, when "expect" is given,
whether the outcome matched. Config comes from the environment exactly like the
server (LEAN_MODE, ANTHROPIC_API_KEY, PROVE_SAMPLES, RETRIEVAL, budgets, ...).
"""
import asyncio, json, pathlib, sys, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "server"))
from app.config import Config                    # noqa: E402
from app.lean.verifier import make_verifier      # noqa: E402
from app.llm import AnthropicLLM, OpenAICompatLLM, RoutedLLM  # noqa: E402
from app.models import Job                       # noqa: E402
from app.orchestrator import Orchestrator        # noqa: E402


def load(path: pathlib.Path) -> list[dict]:
    rows = []
    for i, line in enumerate(path.read_text().splitlines(), 1):
        if not line.strip():
            continue
        row = json.loads(line)
        assert row.get("name") and row.get("problem"), f"line {i}: name and problem required"
        rows.append(row)
    return rows


async def run(rows: list[dict]) -> int:
    cfg = Config()
    if cfg.lean_mode == "fake" or not cfg.anthropic_api_key:
        print("bench needs LEAN_MODE=file|repl and ANTHROPIC_API_KEY (see README Quickstart 2)")
        return 2
    llm = AnthropicLLM(cfg.anthropic_api_key, cfg.chef_model, cfg.worker_model)
    if cfg.prover_base_url and cfg.prover_model:
        llm = RoutedLLM(llm, OpenAICompatLLM(cfg.prover_base_url, cfg.prover_model,
                                             cfg.prover_api_key))
    lean = make_verifier(cfg)
    results, matched, expected = [], 0, 0
    try:
        for row in rows:
            job = Job(problem=row["problem"])
            t0 = time.time()
            await Orchestrator(job, llm, lean, cfg).run()
            dt = time.time() - t0
            ok = None
            if row.get("expect"):
                expected += 1
                ok = (job.status.value == row["expect"])
                matched += ok
            results.append((row["name"], job.status.value, job.llm_calls, job.lean_calls, dt, ok))
            flag = {True: "match", False: "MISMATCH", None: ""}[ok]
            print(f"{row['name']:<22} {job.status.value:<10} "
                  f"llm={job.llm_calls:<4} lean={job.lean_calls:<4} {dt:7.1f}s  {flag}")
    finally:
        await lean.close()
    from collections import Counter
    print("\nsummary:", dict(Counter(r[1] for r in results)))
    if expected:
        print(f"expected-outcome matches: {matched}/{expected}")
    return 0 if (not expected or matched == expected) else 1


def main() -> int:
    args = [a for a in sys.argv[1:] if a != "--dry-run"]
    path = pathlib.Path(args[0]) if args else pathlib.Path(__file__).parent / "bench_problems.jsonl"
    rows = load(path)
    print(f"{len(rows)} problems loaded from {path}")
    if "--dry-run" in sys.argv:
        return 0
    return asyncio.run(run(rows))


if __name__ == "__main__":
    sys.exit(main())
