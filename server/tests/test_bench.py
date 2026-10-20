"""scripts/bench.py: the runner that sends a problem set to a running server."""
import csv
import importlib.util
import json
import pathlib
import socket
import threading
import time

import pytest
import uvicorn

from app.main import create_app
from app.testing import DEMO_PROBLEM, default_fake_lean, demo_config, demo_llm

BENCH_PATH = pathlib.Path(__file__).resolve().parents[2] / "scripts" / "bench.py"
SET_PATH = BENCH_PATH.parent / "bench_problems.jsonl"


def _load_bench():
    spec = importlib.util.spec_from_file_location("bench", BENCH_PATH)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


bench = _load_bench()


def test_outcome_separates_misses_from_wrong_verdicts():
    assert bench.outcome("proved", "proved") == "ok"
    assert bench.outcome("refuted", "refuted") == "ok"
    assert bench.outcome("proved", "exhausted") == "miss"
    assert bench.outcome("refuted", "timeout") == "miss"
    assert bench.outcome("proved", "refuted") == "WRONG"     # a true claim refuted
    assert bench.outcome("refuted", "proved") == "WRONG"     # a false claim proved


def test_shipped_problem_set_is_valid():
    rows = bench.load(SET_PATH)
    assert len(rows) >= 10
    assert {r["expect"] for r in rows} == {"proved", "refuted"}
    assert all(r.get("tier") for r in rows)


def test_load_rejects_bad_rows(tmp_path):
    bad = tmp_path / "bad.jsonl"
    bad.write_text('{"name": "a", "problem": "p", "expect": "maybe"}\n')
    with pytest.raises(ValueError, match="expect"):
        bench.load(bad)
    bad.write_text('{"name": "a", "problem": "p", "expect": "proved"}\n'
                   '{"name": "a", "problem": "q", "expect": "proved"}\n')
    with pytest.raises(ValueError, match="duplicate"):
        bench.load(bad)


def _free_port() -> int:
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


class _LiveServer:
    """The real FastAPI app on a real port, so the runner's urllib client is exercised."""

    def __init__(self, app):
        self.port = _free_port()
        self.server = uvicorn.Server(uvicorn.Config(app, host="127.0.0.1", port=self.port,
                                                    log_level="warning", lifespan="on"))
        self.thread = threading.Thread(target=self.server.run, daemon=True)

    def __enter__(self):
        self.thread.start()
        deadline = time.monotonic() + 10
        while not self.server.started:
            assert time.monotonic() < deadline, "test server did not start"
            time.sleep(0.02)
        return f"http://127.0.0.1:{self.port}"

    def __exit__(self, *exc):
        self.server.should_exit = True
        self.thread.join(timeout=10)


def _real_looking_app():
    # Scripted model + simulated Lean, but reported as a real configuration so the
    # runner accepts it (an injected LLM is used before any fake/demo switch).
    cfg = demo_config()
    cfg.fake_llm, cfg.lean_mode = False, "repl"
    return create_app(cfg, demo_llm(), default_fake_lean())


def test_end_to_end_against_a_live_server(tmp_path, monkeypatch):
    monkeypatch.setattr(bench, "POLL_S", 0.05)
    probs = tmp_path / "one.jsonl"
    probs.write_text(json.dumps({"name": "demo", "tier": "easy", "expect": "proved",
                                 "problem": DEMO_PROBLEM}) + "\n")
    with _LiveServer(_real_looking_app()) as url:
        rc = bench.main([str(probs), "--server", url, "--out", str(tmp_path / "out"),
                         "--rounds", "2", "--repair", "2", "--depth", "2",
                         "--brainstormers", "3"])
    assert rc == 0
    (run_dir,) = (tmp_path / "out").iterdir()
    rows = list(csv.DictReader((run_dir / "results.csv").open()))
    assert [(r["name"], r["status"], r["outcome"]) for r in rows] == [("demo", "proved", "ok")]
    assert int(rows[0]["llm_calls"]) > 0 and int(rows[0]["lean_calls"]) > 0
    summary = (run_dir / "summary.md").read_text()
    assert "1/1 as expected" in summary and "| demo |" in summary
    job = json.loads((run_dir / "jobs" / "demo.json").read_text())
    assert job["status"] == "proved" and len(job["events"]) == job["event_count"]


def test_wrong_verdict_gives_exit_code_1(tmp_path, monkeypatch):
    monkeypatch.setattr(bench, "POLL_S", 0.05)
    probs = tmp_path / "one.jsonl"
    probs.write_text(json.dumps({"name": "demo", "expect": "refuted",
                                 "problem": DEMO_PROBLEM}) + "\n")
    with _LiveServer(_real_looking_app()) as url:
        rc = bench.main([str(probs), "--server", url, "--out", str(tmp_path / "out"),
                         "--rounds", "2", "--repair", "2", "--depth", "2",
                         "--brainstormers", "3"])
    assert rc == 1


def test_refuses_the_offline_demo_server(tmp_path):
    app = create_app(demo_config(), demo_llm(), default_fake_lean())   # fake_llm=True
    with _LiveServer(app) as url:
        rc = bench.main([str(SET_PATH), "--server", url, "--out", str(tmp_path / "out")])
    assert rc == 2
    assert not (tmp_path / "out").exists()


def test_unreachable_server_is_a_clear_error(tmp_path, capsys):
    rc = bench.main([str(SET_PATH), "--server", f"http://127.0.0.1:{_free_port()}",
                     "--out", str(tmp_path / "out")])
    assert rc == 2
    assert "Start it first" in capsys.readouterr().out
