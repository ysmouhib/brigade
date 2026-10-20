"""Console progress lines for the server terminal (model calls, Lean checks, waits).

The web UI shows agent events, but a long model call or the first Mathlib import emits
nothing until it finishes. These lines show what the server is waiting on, and for how long.
"""
from __future__ import annotations
import logging
import sys

log = logging.getLogger("brigade")
if not log.handlers:
    _h = logging.StreamHandler(sys.stderr)
    _h.setFormatter(logging.Formatter("%(asctime)s brigade  %(message)s", "%H:%M:%S"))
    log.addHandler(_h)
    log.setLevel(logging.INFO)
    log.propagate = False
