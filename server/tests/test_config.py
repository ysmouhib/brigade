"""Configuration must parse what users actually write, and fail loudly on what it cannot use.

Background: scripts/run_server.ps1 used to keep inline `# comments` from .env, so on
Windows `LEAN_MODE=file   # ...` silently selected the fake verifier, and
`PROVE_SAMPLES=1   # ...` crashed startup. A fake verifier must never judge a real model.
"""
from __future__ import annotations
import shutil
import subprocess
from pathlib import Path

import pytest

from app.config import Config
from app.lean.verifier import FakeLean, make_verifier
from app.main import create_app

ROOT = Path(__file__).resolve().parents[2]


def test_inline_comments_and_quotes_are_ignored(monkeypatch):
    monkeypatch.setenv("LEAN_MODE", "file            # fake | file | repl")
    monkeypatch.setenv("PROVE_SAMPLES", "4   # parallel candidates")
    monkeypatch.setenv("TACTIC_CASCADE", "1  # try omega first")
    monkeypatch.setenv("CHEF_MODEL", '"claude-opus-4-8"   # chef / strategist / critic')
    monkeypatch.setenv("BRIGADE_DB", "# e.g. jobs.db")   # what a trimming loader leaves behind
    monkeypatch.setenv("AUTH_TOKEN", '"abc#def"')         # a '#' inside a value is kept
    cfg = Config()
    assert (cfg.lean_mode, cfg.prove_samples, cfg.tactic_cascade) == ("file", 4, True)
    assert (cfg.chef_model, cfg.db_path, cfg.auth_token) == ("claude-opus-4-8", "", "abc#def")


@pytest.mark.parametrize("name,value", [("LEAN_MODE", "lean"), ("VERIFY_POLICY", "fast"),
                                        ("RETRIEVAL", "google")])
def test_unknown_mode_values_fail_loudly(monkeypatch, name, value):
    monkeypatch.setenv(name, value)
    with pytest.raises(ValueError, match=name):
        Config()


def test_relative_lean_paths_resolve_against_the_repository_root(monkeypatch):
    """.env lives at the repo root and says ./lean/...; the server runs from server/."""
    monkeypatch.chdir(ROOT / "server")
    monkeypatch.setenv("LEAN_PROJECT_DIR", "./lean/BrigadeLean")
    monkeypatch.setenv("LEAN_REPL_BIN", "./lean/repl/.lake/build/bin/repl")
    cfg = Config()
    assert Path(cfg.lean_project_dir) == ROOT / "lean" / "BrigadeLean"
    assert Path(cfg.lean_repl_bin) == ROOT / "lean" / "repl" / ".lake" / "build" / "bin" / "repl"


def test_default_lean_project_is_the_one_setup_creates(monkeypatch):
    monkeypatch.delenv("LEAN_PROJECT_DIR", raising=False)
    monkeypatch.chdir(ROOT / "server")
    assert Path(Config().lean_project_dir) == ROOT / "lean" / "BrigadeLean"


def test_bad_integers_name_the_variable(monkeypatch):
    monkeypatch.setenv("MAX_ROUNDS", "two")
    with pytest.raises(ValueError, match="MAX_ROUNDS"):
        Config()


def test_unknown_lean_mode_never_falls_back_to_the_fake_verifier():
    cfg = Config()
    cfg.lean_mode = "bogus"
    with pytest.raises(ValueError, match="LEAN_MODE"):
        make_verifier(cfg)


async def test_real_claude_jobs_refuse_the_fake_verifier():
    """With a key but LEAN_MODE=fake, a real job would be 'proved' by the simulator."""
    import httpx
    cfg = Config()
    cfg.fake_llm, cfg.lean_mode, cfg.anthropic_api_key = False, "fake", "sk-ant-test"
    app = create_app(cfg)
    async with app.router.lifespan_context(app):
        assert isinstance(app.state.lean, FakeLean)
        async with httpx.AsyncClient(transport=httpx.ASGITransport(app=app),
                                     base_url="http://t") as c:
            r = await c.post("/jobs", json={"problem": "Prove that 1 + 1 = 2.", "demo": False})
    assert r.status_code == 409 and "LEAN_MODE" in r.json()["detail"]


def test_env_example_has_no_inline_comments_and_parses(monkeypatch):
    for line in (ROOT / ".env.example").read_text(encoding="utf-8").splitlines():
        s = line.strip()
        if not s or s.startswith("#"):
            continue
        key, _, value = s.partition("=")
        assert "#" not in value, f"inline comment on {key}: put comments on their own line"
        monkeypatch.setenv(key.strip(), value.strip())
    Config()   # every example value must be accepted as written


@pytest.mark.skipif(not (shutil.which("pwsh") or shutil.which("powershell")),
                    reason="PowerShell not installed (runs on Windows machines)")
def test_powershell_loader_strips_inline_comments(tmp_path):
    env = tmp_path / ".env"
    env.write_text("LEAN_MODE=file   # fake | file | repl\n"
                   "BRIGADE_DB=      # e.g. jobs.db\n"
                   'AUTH_TOKEN="abc#def"\n'
                   "# a whole-line comment\n", encoding="utf-8")
    exe = shutil.which("pwsh") or shutil.which("powershell")
    loader = ROOT / "scripts" / "load_env.ps1"
    cmd = (f". '{loader}'; Import-DotEnv '{env}'; "
           "Write-Output \"$env:LEAN_MODE|$env:BRIGADE_DB|$env:AUTH_TOKEN\"")
    out = subprocess.run([exe, "-NoProfile", "-ExecutionPolicy", "Bypass", "-Command", cmd],
                         capture_output=True, text=True, timeout=120)
    assert out.stdout.strip() == "file||abc#def", out.stderr
