"""The numeric Skeptic must never freeze the server, and must say what it is.

Before: probes ran synchronously on the asyncio event loop with any integer the LLM
proposed. A factorial probe at n = 1,000,000 took ~7 s (measured), during which every
job and the HTTP API stood still; larger values effectively never return.
"""
from __future__ import annotations
import asyncio
import json
import time

import pytest

from app import numeric
from app.llm import ScriptedLLM
from app.models import Job, JobStatus
from app.orchestrator import Orchestrator
from app.testing import default_fake_lean, demo_config

PRIME_IS_ODD = "Or(Not(isprime({n})), Eq(Mod({n}, 2), 1))"


def test_oversized_candidates_are_skipped_not_evaluated():
    t0 = time.monotonic()
    assert numeric.find_counterexample("Ge(factorial({n}), {n})", [{"n": 10 ** 100}]) is None
    assert time.monotonic() - t0 < 1.0
    # values inside the cap still work
    assert numeric.find_counterexample(PRIME_IS_ODD, [{"n": 10 ** 7}, {"n": 2}]) == {"n": 2}


async def test_runaway_probe_times_out_while_the_event_loop_keeps_running():
    ticks = 0

    async def ticker():
        nonlocal ticks
        while True:
            await asyncio.sleep(0.05)
            ticks += 1

    t = asyncio.create_task(ticker())
    t0 = time.monotonic()
    with pytest.raises(numeric.ProbeError, match="timed out"):
        # within the cap, but ~7 s of work: the worker must be stopped at the timeout
        await numeric.find_counterexample_async("Ge(factorial({n}), 1)", [{"n": 10 ** 6}],
                                                timeout_s=1.0)
    elapsed = time.monotonic() - t0
    t.cancel()
    assert elapsed < 5.0, f"timeout not enforced ({elapsed:.1f}s)"
    assert ticks >= 5, "the event loop was blocked during the probe"


async def test_worker_recovers_after_a_timeout():
    with pytest.raises(numeric.ProbeError):
        await numeric.find_counterexample_async("Ge(factorial({n}), 1)", [{"n": 10 ** 6}],
                                                timeout_s=0.5)
    cex = await numeric.find_counterexample_async(PRIME_IS_ODD, [{"n": k} for k in range(1, 8)])
    assert cex == {"n": 2}


async def test_refutation_is_labeled_numeric_not_lean_checked():
    def handler(role, user, n):
        if role == "skeptic":
            return json.dumps({"is_checkable": True, "claim_expr": PRIME_IS_ODD,
                               "candidates": [{"n": k} for k in range(1, 8)], "notes": ""})
        return json.dumps({"report": "refuted"})

    job = Job(problem="Prove that every prime number is odd.")
    await Orchestrator(job, ScriptedLLM(handler), default_fake_lean(), demo_config()).run()
    assert job.status == JobStatus.REFUTED
    assert job.refutation.method == "numeric" and job.refutation.lean_checked is False
    refuted = next(e for e in job.events if e.type == "refuted")
    assert "not Lean-checked" in refuted.content
