"""Lean must never be left running in the background.

`lake env <repl>` runs the REPL as a CHILD of lake. Killing only lake orphaned the
REPL, which kept importing Mathlib; on a real machine each timeout left one more
orphan competing for disk and memory, so the next import was slower still.
"""
from __future__ import annotations
import asyncio
import os
import sys

import pytest

from app.lean.verifier import ReplLeanVerifier, kill_process_tree, spawn_process_group

posix_only = pytest.mark.skipif(os.name != "posix", reason="process groups are POSIX")


def _alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    with open(f"/proc/{pid}/stat") as f:      # a zombie is dead too
        return f.read().split()[2] != "Z"


@posix_only
async def test_killing_the_wrapper_kills_its_child_too():
    # a wrapper (like `lake env`) that starts a long-running child and waits for it
    proc = await spawn_process_group(sys.executable, "-c",
        "import subprocess,sys,time; c=subprocess.Popen(['sleep','300']); print(c.pid, flush=True); c.wait()",
        stdout=asyncio.subprocess.PIPE)
    child = int((await proc.stdout.readline()).decode())
    assert _alive(child)
    await kill_process_tree(proc)
    await asyncio.sleep(0.2)
    assert not _alive(child), "the grandchild survived: it would keep loading Mathlib"


async def test_mathlib_import_gets_the_long_startup_allowance():
    seen = []

    class Stub(ReplLeanVerifier):
        async def _spawn(self):
            class P:
                returncode = None
                pid = -1
            self._proc = P()

        async def _roundtrip(self, obj, timeout):
            seen.append((obj["cmd"].splitlines()[0], timeout))
            return {"env": 0}

    v = Stub(project_dir=".", repl_bin="repl", timeout_s=180, startup_timeout_s=1200)
    assert not v.ready
    await v.warm_up()
    assert v.ready and seen == [("import Mathlib", 1200)]


async def test_killed_process_leaves_no_open_pipes_behind():
    """Ctrl+C on the server printed 'RuntimeError: Event loop is closed': the REPL's
    stdin pipe stayed open and was only closed by the garbage collector, after the loop."""
    proc = await spawn_process_group(sys.executable, "-c", "import time; time.sleep(30)",
                                     stdin=asyncio.subprocess.PIPE,
                                     stdout=asyncio.subprocess.PIPE)
    await kill_process_tree(proc)
    assert proc.returncode is not None
    assert proc._transport.is_closing()        # closed now, while the loop still runs
