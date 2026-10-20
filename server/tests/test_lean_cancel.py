"""Cancelling a job in the middle of a Lean check must not corrupt later checks.

The REPL answers commands strictly in order over one pipe. If the job waiting for an
answer is cancelled and nobody reads that answer, the NEXT check reads it as its own:
every later reply is shifted by one, so a proof could be judged by the result of an
earlier command. Cancellations happen in practice: the UI's Cancel button and the bench
runner's per-problem timeout both cancel running jobs.
"""
from __future__ import annotations
import asyncio
import os
import sys
import textwrap

import pytest

from app.lean import verifier as vmod
from app.lean.verifier import FileLeanVerifier, ReplLeanVerifier, spawn_process_group

# A stand-in for leanprover-community/repl: blank-line-separated JSON commands in, one
# JSON reply (plus a blank line) out, in order. Commands containing SLOW take a while.
FAKE_REPL = textwrap.dedent('''
    import json, sys, time
    n, buf = 0, ""
    for line in sys.stdin:
        if line.strip():
            buf += line
            continue
        if not buf:
            continue
        cmd, buf = json.loads(buf)["cmd"], ""
        n += 1
        if "SLOW" in cmd:
            time.sleep(0.6)
        first = cmd.splitlines()[0]
        print(json.dumps({"env": n, "messages": [{"severity": "info", "data": "echo: " + first}]}))
        print(flush=True)
''')


class _ProcessRepl(ReplLeanVerifier):
    """The real ReplLeanVerifier talking to FAKE_REPL instead of `lake env repl`."""

    def __init__(self, script: str):
        super().__init__(project_dir=".", repl_bin="unused", timeout_s=10, startup_timeout_s=10)
        self.script, self.spawns = script, 0

    async def _spawn(self):
        self.spawns += 1
        self._proc = await spawn_process_group(
            sys.executable, self.script, stdin=asyncio.subprocess.PIPE,
            stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.DEVNULL, limit=2 ** 24)


@pytest.fixture
def repl(tmp_path):
    script = tmp_path / "fake_repl.py"
    script.write_text(FAKE_REPL)
    return _ProcessRepl(str(script))


async def test_cancelled_check_does_not_shift_later_replies(repl):
    await repl.warm_up()
    slow = asyncio.create_task(repl.check("theorem slow : True := by SLOW"))
    await asyncio.sleep(0.2)                 # the command is out; its reply is not back yet
    slow.cancel()
    with pytest.raises(asyncio.CancelledError):
        await slow
    res = await repl.check("theorem next_one : True := by trivial")
    assert res.infos == ["echo: theorem next_one : True := by trivial"]
    again = await repl.check("theorem third : True := by trivial")
    assert again.infos == ["echo: theorem third : True := by trivial"]
    # and the warm REPL was kept: no second Mathlib load
    assert repl.spawns == 1
    await repl.close()


async def test_close_while_a_check_is_in_flight_finishes_cleanly(repl):
    await repl.warm_up()
    slow = asyncio.create_task(repl.check("theorem slow : True := by SLOW"))
    await asyncio.sleep(0.2)
    await repl.close()
    res = await slow
    assert not res.ok                        # reported as an infrastructure failure
    assert not repl._inflight


def _alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    with open(f"/proc/{pid}/stat") as f:      # a zombie is dead too
        return f.read().split()[2] != "Z"


@pytest.mark.skipif(os.name != "posix", reason="uses /proc")
async def test_cancelled_file_check_stops_its_lean_process(tmp_path, monkeypatch):
    started = []

    async def fake_spawn(*args, **kw):      # stands in for `lake env lean <file>`
        proc = await spawn_process_group(sys.executable, "-c", "import time; time.sleep(30)",
                                         stdout=kw.get("stdout"), stderr=kw.get("stderr"))
        started.append(proc)
        return proc
    monkeypatch.setattr(vmod, "spawn_process_group", fake_spawn)
    v = FileLeanVerifier(str(tmp_path), timeout_s=60)
    task = asyncio.create_task(v.check("theorem t : True := by trivial"))
    while not started:
        await asyncio.sleep(0.02)
    task.cancel()
    with pytest.raises(asyncio.CancelledError):
        await task
    assert not _alive(started[0].pid)
