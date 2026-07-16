"""FastAPI entrypoint + built-in web UI.

create_app(cfg, llm, lean) takes optional injected components so tests can pass
deterministic fakes; production wiring reads everything from the environment.

Key UX decisions:
  * The server boots WITHOUT an API key. The web UI (served at "/") offers a Settings
    panel to paste one (optionally remembered in .env) — or every job can run on the
    built-in offline demo engine so people can see the machinery instantly.
  * The Lean verifier is created ONCE and shared across jobs (warm REPL survives);
    it is closed on app shutdown, not per job.
"""
from __future__ import annotations
import asyncio
import contextlib
import os
from dataclasses import replace
from pathlib import Path
from typing import Optional

from fastapi import Depends, FastAPI, Header, HTTPException
from fastapi.responses import FileResponse
from pydantic import BaseModel

from .config import Config
from .lean.verifier import LeanVerifier, make_verifier
from .llm import LLM, AnthropicLLM, OpenAICompatLLM, RoutedLLM
from .models import Job, JobStatus, NewJobRequest
from .orchestrator import Orchestrator
from .store import Store

STATIC_DIR = Path(__file__).parent / "static"


class SettingsUpdate(BaseModel):
    api_key: Optional[str] = None
    remember: bool = False


def _persist_key_to_env(key: str) -> str:
    """Write ANTHROPIC_API_KEY into <repo>/.env (0600). Returns the path written."""
    env_path = Path(__file__).resolve().parents[2] / ".env"
    lines = []
    if env_path.exists():
        lines = [ln for ln in env_path.read_text().splitlines()
                 if not ln.startswith("ANTHROPIC_API_KEY=")]
    lines.append(f"ANTHROPIC_API_KEY={key}")
    env_path.write_text("\n".join(lines) + "\n")
    os.chmod(env_path, 0o600)
    return str(env_path)


def create_app(cfg: Optional[Config] = None,
               llm: Optional[LLM] = None,
               lean: Optional[LeanVerifier] = None) -> FastAPI:
    cfg = cfg or Config()

    @contextlib.asynccontextmanager
    async def lifespan(app: FastAPI):
        app.state.injected_llm = llm
        app.state.real_llm = None          # built lazily once a key exists
        app.state.real_llm_key = ""
        if lean is not None:
            app.state.lean = lean
        elif cfg.fake_llm and cfg.lean_mode == "fake":
            from .testing import default_fake_lean
            app.state.lean = default_fake_lean()
        else:
            app.state.lean = make_verifier(cfg)
        app.state.store = Store(cfg.db_path)
        try:
            yield
        finally:
            await app.state.store.shutdown()
            with contextlib.suppress(Exception):
                await app.state.lean.close()

    app = FastAPI(title="Brigade", version="2.0", lifespan=lifespan)

    async def auth(authorization: str = Header(default="")):
        if cfg.auth_token and authorization != f"Bearer {cfg.auth_token}":
            raise HTTPException(401, "bad or missing bearer token")

    def _job_or_404(job_id: str) -> Job:
        job = app.state.store.get(job_id)
        if job is None:
            raise HTTPException(404, f"no such job {job_id}")
        return job

    def _engine_for(req: NewJobRequest):
        """Pick (engine_name, llm, lean) for one job. Demo is always available."""
        if req.demo:
            from .testing import default_fake_lean, demo_llm
            return "demo", demo_llm(), default_fake_lean()
        if app.state.injected_llm is not None:
            return "claude", app.state.injected_llm, app.state.lean
        if cfg.fake_llm:
            from .testing import default_fake_lean, demo_llm
            return "demo", demo_llm(), default_fake_lean()
        if not cfg.anthropic_api_key:
            raise HTTPException(409, "No Anthropic API key configured. Open Settings and "
                                     "paste your key, or tick 'offline demo' for this job.")
        if app.state.real_llm is None or app.state.real_llm_key != cfg.anthropic_api_key:
            llm_: LLM = AnthropicLLM(cfg.anthropic_api_key, cfg.chef_model, cfg.worker_model)
            if cfg.prover_base_url and cfg.prover_model:
                llm_ = RoutedLLM(llm_, OpenAICompatLLM(cfg.prover_base_url, cfg.prover_model,
                                                       cfg.prover_api_key))
            app.state.real_llm = llm_
            app.state.real_llm_key = cfg.anthropic_api_key
        return "claude", app.state.real_llm, app.state.lean

    # ------------------------------------------------------------------ routes
    @app.get("/")
    async def index():
        return FileResponse(STATIC_DIR / "index.html")

    @app.get("/health")
    async def health():
        return {"ok": True,
                "lean_mode": cfg.lean_mode,
                "llm_mode": "fake" if cfg.fake_llm else "anthropic",
                "has_key": bool(cfg.anthropic_api_key) or cfg.fake_llm
                           or app.state.injected_llm is not None,
                "verify_policy": cfg.verify_policy,
                "retrieval": cfg.retrieval,
                "prover_backend": bool(cfg.prover_base_url),
                "persistent": bool(cfg.db_path)}

    @app.get("/settings", dependencies=[Depends(auth)])
    async def get_settings():
        return {"has_key": bool(cfg.anthropic_api_key),
                "fake_llm": cfg.fake_llm,
                "lean_mode": cfg.lean_mode,
                "chef_model": cfg.chef_model,
                "worker_model": cfg.worker_model,
                "verify_policy": cfg.verify_policy}

    @app.post("/settings", dependencies=[Depends(auth)])
    async def update_settings(upd: SettingsUpdate):
        saved_to = None
        if upd.api_key is not None:
            cfg.anthropic_api_key = upd.api_key.strip()
            app.state.real_llm = None      # rebuild with the new key on next job
            if upd.remember and cfg.anthropic_api_key:
                saved_to = _persist_key_to_env(cfg.anthropic_api_key)
        return {"has_key": bool(cfg.anthropic_api_key), "saved_to": saved_to}

    @app.post("/jobs", dependencies=[Depends(auth)])
    async def new_job(req: NewJobRequest):
        problem = req.problem.strip()
        if not problem:
            raise HTTPException(422, "problem must be non-empty")
        engine, job_llm, job_lean = _engine_for(req)
        if engine == "demo":
            from .testing import DEMO_PROBLEM
            if problem != DEMO_PROBLEM:
                raise HTTPException(409,
                    "The replay engine runs one fixed, recorded scenario "
                    f"({DEMO_PROBLEM!r}) so every mechanism is visible — it does not "
                    "read custom input. For your own claims use the Claude + Lean "
                    "engine (API key + local Lean), or the in-browser simulated demo "
                    "on the project website.")
        job_cfg = replace(cfg)
        if engine == "demo":
            job_cfg.fake_llm, job_cfg.lean_mode, job_cfg.verify_policy = True, "fake", "full"
            job_cfg.tactic_cascade, job_cfg.prove_samples, job_cfg.retrieval = False, 1, "off"
        if req.verify_policy in ("full", "strategic"):
            job_cfg.verify_policy = req.verify_policy
        if req.budgets:
            for k, v in req.budgets.model_dump(exclude_none=True).items():
                setattr(job_cfg, k, max(1, min(int(v), 16)))
        job = Job(problem=problem, engine=engine)
        orch = Orchestrator(job, job_llm, job_lean, job_cfg)
        task = asyncio.create_task(orch.run(), name=f"job-{job.id}")
        app.state.store.add(job, task)
        return {"job_id": job.id, "engine": engine}

    @app.get("/jobs", dependencies=[Depends(auth)])
    async def list_jobs():
        out = []
        for job in sorted(app.state.store.jobs.values(),
                          key=lambda j: j.created_at, reverse=True):
            out.append({"id": job.id, "status": job.status, "phase": job.phase,
                        "round": job.round, "created_at": job.created_at,
                        "engine": job.engine,
                        "problem_preview": job.problem[:120]})
        return {"jobs": out}

    @app.get("/jobs/{job_id}", dependencies=[Depends(auth)])
    async def get_job(job_id: str):
        job = _job_or_404(job_id)
        nodes = [{"id": n.id, "parent_id": n.parent_id, "depth": n.depth,
                  "kind": n.kind, "lean_name": n.lean_name, "informal": n.informal,
                  "lean_statement": n.lean_statement, "status": n.status,
                  "attempts": n.attempts}
                 for n in job.nodes.values()]
        return {"id": job.id, "status": job.status, "phase": job.phase,
                "round": job.round, "problem": job.problem, "engine": job.engine,
                "final_lean": job.final_lean,
                "refutation": job.refutation.model_dump() if job.refutation else None,
                "summary": job.summary, "nodes": nodes,
                "llm_calls": job.llm_calls, "lean_calls": job.lean_calls,
                "event_count": len(job.events)}

    @app.get("/jobs/{job_id}/events", dependencies=[Depends(auth)])
    async def get_events(job_id: str, since: int = 0, limit: int = 200):
        job = _job_or_404(job_id)
        limit = max(1, min(limit, 500))
        evs = [e for e in job.events if e.seq > since][:limit]
        nxt = evs[-1].seq if evs else since
        return {"events": [e.model_dump() for e in evs], "next": nxt,
                "job_status": job.status}

    @app.post("/jobs/{job_id}/cancel", dependencies=[Depends(auth)])
    async def cancel_job(job_id: str):
        job = _job_or_404(job_id)
        if job.status in (JobStatus.QUEUED, JobStatus.RUNNING):
            app.state.store.cancel(job_id)
            return {"cancelled": True}
        return {"cancelled": False, "status": job.status}

    return app


app = create_app()  # uvicorn app.main:app
