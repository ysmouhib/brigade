"""Benchmark runner executing Hales-Jewett & Van der Waerden claims against real Lean 4."""

from __future__ import annotations

import json
from pathlib import Path
import tempfile
import time
from typing import Any

from .lean_verifier import RealLeanVerifier
from .llm import LLM, MultiProviderLLM, ProviderConfig, ScriptedLLM
from .models import Job
from .orchestrator import Orchestrator, OrchestratorConfig


async def run_benchmark_suite(
    project_dir: Path,
    suite_path: Path,
    live_llm: bool = False,
) -> tuple[list[dict[str, Any]], bool]:
    """Run every entry in `suite_path` JSONL through `Orchestrator` + `RealLeanVerifier`."""
    verifier = RealLeanVerifier(project_dir, timeout_s=60.0)
    if live_llm:
        llm: LLM = MultiProviderLLM(ProviderConfig.from_env())
    else:
        llm = ScriptedLLM(lambda role, _s, _u: {"is_hj_finite_query": False} if role == "skeptic" else {})

    entries = [
        json.loads(line)
        for line in suite_path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]

    results: list[dict[str, Any]] = []
    all_ok = True
    with tempfile.TemporaryDirectory() as tmp:
        ledger_file = Path(tmp) / "bench_ledger.json"
        for entry in entries:
            t0 = time.perf_counter()
            cfg = OrchestratorConfig(
                project_dir=project_dir,
                max_rounds=1 if not live_llm else 3,
                ledger_path=ledger_file,
            )
            job = Job(problem=entry["problem"])
            await Orchestrator(job, llm, verifier, cfg).run()
            elapsed = time.perf_counter() - t0
            passed = job.status.value == entry["expected"]
            if not passed:
                all_ok = False
            results.append(
                {
                    "id": entry["id"],
                    "expected": entry["expected"],
                    "actual": job.status.value,
                    "passed": passed,
                    "lean_calls": job.lean_calls,
                    "llm_calls": job.llm_calls,
                    "elapsed_s": round(elapsed, 3),
                    "summary": job.summary,
                }
            )
    return results, all_ok
