#!/usr/bin/env python3
"""Benchmark runner: send a problem set to a RUNNING Brigade server and record the results.

It talks to the server over HTTP, so it reuses the server's warm Lean REPL (no second
Mathlib load) and whichever LLM provider the server is configured with. Standard library
only: run it from any terminal that can reach the server.

Usage:
    python3 scripts/bench.py                                # scripts/bench_problems.jsonl
    python3 scripts/bench.py my_set.jsonl --only even_sq    # a subset by name
    python3 scripts/bench.py --repair 3 --rounds 2          # other budgets
    python3 scripts/bench.py --dry-run                      # validate the file only

Problem file, one JSON object per line:
    {"name": str, "problem": str, "expect": "proved" | "refuted", "tier": str (optional)}

Each run writes experiments/results/<date>-<time>-<set>/ with
    results.csv    one row per problem, rewritten after every job (survives Ctrl+C)
    summary.md     the table plus run metadata (git SHA, server config, budgets)
    jobs/<name>.json   the full job and its event log, for diagnosing misses

Outcome per problem: ok (status == expect); miss (no verdict: exhausted, error, timeout);
WRONG (the opposite verdict: a true claim refuted or a false claim proved). The exit
code is 1 if any outcome is WRONG, else 0. Misses are expected in a baseline.
"""
from __future__ import annotations

import argparse
import csv
import datetime as dt
import json
import os
import pathlib
import subprocess
import sys
import time
import urllib.error
import urllib.request

REPO = pathlib.Path(__file__).resolve().parents[1]
DEFAULT_SET = pathlib.Path(__file__).parent / "bench_problems.jsonl"
TERMINAL = {"proved", "refuted", "exhausted", "cancelled", "error"}
POLL_S = 3.0          # seconds between status polls
FIELDS = ["name", "tier", "expect", "status", "outcome", "seconds", "llm_calls",
          "lean_calls", "detail", "job_id"]


# ------------------------------------------------------------------ pure helpers
def load(path: pathlib.Path) -> list[dict]:
    rows, seen = [], set()
    for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip():
            continue
        row = json.loads(line)
        if not (row.get("name") and row.get("problem")):
            raise ValueError(f"{path}:{i}: 'name' and 'problem' are required")
        if row.get("expect") not in ("proved", "refuted"):
            raise ValueError(f"{path}:{i}: 'expect' must be 'proved' or 'refuted'")
        if row["name"] in seen:
            raise ValueError(f"{path}:{i}: duplicate name {row['name']!r}")
        seen.add(row["name"])
        rows.append(row)
    return rows


def outcome(expect: str, status: str) -> str:
    if status == expect:
        return "ok"
    if {expect, status} == {"proved", "refuted"}:
        return "WRONG"
    return "miss"


def summarize(results: list[dict]) -> dict:
    n = len(results)
    by = lambda key, val: sum(1 for r in results if r[key] == val)  # noqa: E731
    return {"problems": n, "ok": by("outcome", "ok"), "miss": by("outcome", "miss"),
            "wrong": by("outcome", "WRONG"),
            "proved": by("status", "proved"), "refuted": by("status", "refuted"),
            "seconds": round(sum(float(r["seconds"]) for r in results), 1),
            "llm_calls": sum(int(r["llm_calls"]) for r in results),
            "lean_calls": sum(int(r["lean_calls"]) for r in results)}


def markdown(results: list[dict], meta: dict) -> str:
    s = summarize(results)
    lines = [f"# Bench run {meta['run']}", "",
             f"- Problem set: `{meta['set']}`",
             f"- Git: `{meta['git']}`",
             f"- Server: {meta['server_desc']}",
             f"- Budgets: {meta['budgets_desc']}",
             f"- Result: **{s['ok']}/{s['problems']} as expected**, {s['miss']} miss, "
             f"{s['wrong']} wrong; {s['seconds']} s, {s['llm_calls']} LLM calls, "
             f"{s['lean_calls']} Lean calls in total",
             "",
             "| Problem | Tier | Expect | Status | Outcome | Time (s) | LLM calls | Lean calls | Detail |",
             "| --- | --- | --- | --- | --- | --- | --- | --- | --- |"]
    for r in results:
        detail = str(r["detail"]).replace("|", "\\|").replace("\n", " ")
        lines.append(f"| {r['name']} | {r['tier']} | {r['expect']} | {r['status']} | "
                     f"{r['outcome']} | {r['seconds']} | {r['llm_calls']} | "
                     f"{r['lean_calls']} | {detail} |")
    return "\n".join(lines) + "\n"


def detail_of(job: dict) -> str:
    if job.get("refutation"):
        ref = job["refutation"]
        how = "Lean-checked" if ref.get("lean_checked") else "numeric"
        return f"counterexample {ref.get('counterexample')} ({how})"
    if job.get("status") == "proved":
        return "Lean-verified"
    return (job.get("summary") or "")[:160]


# ------------------------------------------------------------------ server client
class Server:
    def __init__(self, base: str, token: str = ""):
        self.base, self.token = base.rstrip("/"), token

    def call(self, method: str, path: str, body: dict | None = None) -> dict:
        req = urllib.request.Request(self.base + path, method=method,
                                     data=None if body is None else json.dumps(body).encode())
        req.add_header("Content-Type", "application/json")
        if self.token:
            req.add_header("Authorization", f"Bearer {self.token}")
        try:
            with urllib.request.urlopen(req, timeout=30) as resp:
                return json.loads(resp.read())
        except urllib.error.HTTPError as e:
            raise RuntimeError(f"{method} {path} -> HTTP {e.code}: "
                               f"{e.read().decode(errors='replace')[:300]}") from None

    def events(self, job_id: str) -> list[dict]:
        out, since = [], 0
        while True:
            page = self.call("GET", f"/jobs/{job_id}/events?since={since}&limit=500")
            out += page["events"]
            if not page["events"]:
                return out
            since = page["next"]


def git_sha() -> str:
    try:
        sha = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=REPO,
                             capture_output=True, text=True, timeout=10).stdout.strip()
        dirty = subprocess.run(["git", "status", "--porcelain", "--untracked-files=no"],
                               cwd=REPO, capture_output=True, text=True, timeout=10).stdout.strip()
        return (sha or "unknown") + ("+dirty" if dirty else "")
    except (OSError, subprocess.SubprocessError):
        return "unknown"


def wait_until_ready(srv: Server, max_wait_s: float) -> dict:
    t0 = time.monotonic()
    said = False
    while True:
        h = srv.call("GET", "/health")
        if h.get("lean_ready", True):
            return h
        if not said:
            print("Server is still loading Mathlib; waiting for it to be ready ...", flush=True)
            said = True
        if time.monotonic() - t0 > max_wait_s:
            raise RuntimeError("the server's Lean REPL did not become ready in time")
        time.sleep(10)


def run_one(srv: Server, row: dict, budgets: dict, timeout_s: float) -> tuple[dict, dict]:
    t0 = time.monotonic()
    job_id = srv.call("POST", "/jobs", {"problem": row["problem"], "budgets": budgets})["job_id"]
    status, job = "running", {}
    while True:
        time.sleep(POLL_S)
        job = srv.call("GET", f"/jobs/{job_id}")
        status = job["status"]
        if status in TERMINAL:
            break
        if time.monotonic() - t0 > timeout_s:
            srv.call("POST", f"/jobs/{job_id}/cancel")
            status = "timeout"
            break
    secs = round(time.monotonic() - t0, 1)
    rec = {"name": row["name"], "tier": row.get("tier", ""), "expect": row["expect"],
           "status": status, "outcome": outcome(row["expect"], status), "seconds": secs,
           "llm_calls": job.get("llm_calls", 0), "lean_calls": job.get("lean_calls", 0),
           "detail": "cancelled after timeout" if status == "timeout" else detail_of(job),
           "job_id": job_id}
    return rec, job


def write_csv(path: pathlib.Path, results: list[dict]) -> None:
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=FIELDS)
        w.writeheader()
        w.writerows(results)


# ------------------------------------------------------------------ main
def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("problems", nargs="?", default=str(DEFAULT_SET))
    ap.add_argument("--server", default=os.environ.get("BRIGADE_URL", "http://localhost:8811"))
    ap.add_argument("--token", default=os.environ.get("AUTH_TOKEN", ""))
    ap.add_argument("--only", default="", help="comma-separated problem names to run")
    ap.add_argument("--rounds", type=int, default=1)
    ap.add_argument("--repair", type=int, default=2)
    ap.add_argument("--depth", type=int, default=1)
    ap.add_argument("--brainstormers", type=int, default=1)
    ap.add_argument("--timeout", type=float, default=900, help="seconds per problem")
    ap.add_argument("--out", default=str(REPO / "experiments" / "results"))
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args(argv)

    path = pathlib.Path(a.problems)
    rows = load(path)
    if a.only:
        wanted = {n.strip() for n in a.only.split(",") if n.strip()}
        unknown = wanted - {r["name"] for r in rows}
        if unknown:
            print(f"unknown problem name(s): {', '.join(sorted(unknown))}")
            return 2
        rows = [r for r in rows if r["name"] in wanted]
    print(f"{len(rows)} problem(s) from {path}")
    if a.dry_run:
        return 0

    srv = Server(a.server, a.token)
    try:
        health = wait_until_ready(srv, max_wait_s=1500)
    except (OSError, RuntimeError) as e:
        print(f"Cannot use the server at {a.server}: {e}\n"
              "Start it first (bash scripts/run_server.sh) and wait for 'Lean REPL: ready'.")
        return 2
    if health.get("llm_mode") == "fake" or health.get("lean_mode") == "fake":
        print("The server runs the offline demo (FAKE_LLM or LEAN_MODE=fake); a benchmark "
              "needs a real model and real Lean.")
        return 2

    budgets = {"max_rounds": a.rounds, "repair_cycles": a.repair, "max_depth": a.depth,
               "n_brainstormers": a.brainstormers}
    run = dt.datetime.now().strftime("%Y%m%d-%H%M")
    out = pathlib.Path(a.out) / f"{run}-{path.stem}"
    (out / "jobs").mkdir(parents=True, exist_ok=True)
    models = "/".join(x for x in (health.get("chef_model"), health.get("worker_model")) if x)
    meta = {"run": run, "set": path.name, "git": git_sha(),
            "server_desc": f"{health.get('llm_mode')} {models}".strip()
                           + f", LEAN_MODE={health.get('lean_mode')}, "
                             f"verify_policy={health.get('verify_policy')}",
            "budgets_desc": ", ".join(f"{k}={v}" for k, v in budgets.items())
                            + f", timeout={a.timeout:g}s per problem"}
    print(f"Writing results to {out}\n")
    print(f"{'problem':<22} {'expect':<8} {'status':<10} {'outcome':<7} {'time':>7}  calls")

    results: list[dict] = []
    try:
        for row in rows:
            rec, job = run_one(srv, row, budgets, a.timeout)
            results.append(rec)
            write_csv(out / "results.csv", results)
            try:
                job["events"] = srv.events(rec["job_id"])
            except RuntimeError:
                pass
            (out / "jobs" / f"{row['name']}.json").write_text(
                json.dumps(job, indent=1, ensure_ascii=False), encoding="utf-8")
            print(f"{rec['name']:<22} {rec['expect']:<8} {rec['status']:<10} "
                  f"{rec['outcome']:<7} {rec['seconds']:>6.0f}s  "
                  f"llm={rec['llm_calls']} lean={rec['lean_calls']}", flush=True)
    except KeyboardInterrupt:
        print("\nInterrupted; keeping the results so far.")
    except (OSError, RuntimeError) as e:
        print(f"\nStopped: lost contact with the server ({e}); keeping the results so far.")

    if results:
        (out / "summary.md").write_text(markdown(results, meta), encoding="utf-8")
        s = summarize(results)
        print(f"\n{s['ok']}/{s['problems']} as expected, {s['miss']} miss, {s['wrong']} WRONG; "
              f"{s['seconds']} s, {s['llm_calls']} LLM calls, {s['lean_calls']} Lean calls")
        print(f"Table: {out / 'summary.md'}")
    return 1 if any(r["outcome"] == "WRONG" for r in results) else 0


if __name__ == "__main__":
    sys.exit(main())
