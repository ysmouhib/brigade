"""API tests: drive the FastAPI app over ASGI exactly like the web UI does."""
import asyncio

import httpx

from app.config import Config
from app.main import create_app
from app.testing import DEMO_PROBLEM, default_fake_lean, demo_config, demo_llm


async def _client(app):
    transport = httpx.ASGITransport(app=app)
    return httpx.AsyncClient(transport=transport, base_url="http://test")


async def test_submit_poll_events_like_the_web_ui():
    app = create_app(demo_config(), demo_llm(), default_fake_lean())
    async with app.router.lifespan_context(app):
        async with await _client(app) as c:
            r = await c.get("/health")
            assert r.status_code == 200 and r.json()["ok"] is True

            r = await c.post("/jobs", json={"problem": DEMO_PROBLEM})
            assert r.status_code == 200
            job_id = r.json()["job_id"]

            # poll like the web UI does
            for _ in range(500):
                r = await c.get(f"/jobs/{job_id}")
                body = r.json()
                if body["status"] not in ("queued", "running"):
                    break
                await asyncio.sleep(0.01)
            assert body["status"] == "proved"
            assert body["final_lean"] and "sorry" not in body["final_lean"]
            assert len(body["nodes"]) == 5
            assert {n["status"] for n in body["nodes"]} == {"verified"}

            # events pagination with the `since` cursor
            seen, since = [], 0
            while True:
                r = await c.get(f"/jobs/{job_id}/events", params={"since": since, "limit": 50})
                page = r.json()
                if not page["events"]:
                    break
                seen += page["events"]
                since = page["next"]
            seqs = [e["seq"] for e in seen]
            assert seqs == sorted(seqs) and len(seqs) == len(set(seqs))
            assert len(seen) == body["event_count"]

            # job listing
            r = await c.get("/jobs")
            assert any(j["id"] == job_id and j["status"] == "proved"
                       for j in r.json()["jobs"])

            # cancel after completion is a no-op
            r = await c.post(f"/jobs/{job_id}/cancel")
            assert r.json()["cancelled"] is False

            # 404 path
            assert (await c.get("/jobs/nope")).status_code == 404
            # empty problem rejected
            assert (await c.post("/jobs", json={"problem": "  "})).status_code == 422


class _HangingLLM:
    async def complete(self, **kw):
        await asyncio.sleep(3600)


async def test_cancel_running_job():
    app = create_app(demo_config(), _HangingLLM(), default_fake_lean())
    async with app.router.lifespan_context(app):
        async with await _client(app) as c:
            job_id = (await c.post("/jobs", json={"problem": "hang"})).json()["job_id"]
            await asyncio.sleep(0.05)
            r = await c.post(f"/jobs/{job_id}/cancel")
            assert r.json()["cancelled"] is True
            for _ in range(200):
                status = (await c.get(f"/jobs/{job_id}")).json()["status"]
                if status == "cancelled":
                    break
                await asyncio.sleep(0.01)
            assert status == "cancelled"


async def test_bearer_auth():
    cfg = demo_config()
    cfg.auth_token = "sekrit"
    app = create_app(cfg, demo_llm(), default_fake_lean())
    async with app.router.lifespan_context(app):
        async with await _client(app) as c:
            assert (await c.get("/jobs")).status_code == 401
            r = await c.get("/jobs", headers={"Authorization": "Bearer sekrit"})
            assert r.status_code == 200
            # /health stays open for probes
            assert (await c.get("/health")).status_code == 200


async def test_budget_override_is_clamped():
    app = create_app(demo_config(), demo_llm(), default_fake_lean())
    async with app.router.lifespan_context(app):
        async with await _client(app) as c:
            r = await c.post("/jobs", json={"problem": DEMO_PROBLEM,
                                            "budgets": {"max_rounds": 999}})
            assert r.status_code == 200  # clamped internally, still runs


async def test_web_ui_settings_and_demo_engine():
    """No key configured: UI is served, claude engine is refused with guidance,
    demo engine works, and pasting a key via /settings unlocks the claude path."""
    cfg = demo_config()
    cfg.fake_llm = False            # simulate a fresh real-mode install with no key
    cfg.anthropic_api_key = ""
    app = create_app(cfg, llm=None, lean=default_fake_lean())
    async with app.router.lifespan_context(app):
        async with await _client(app) as c:
            r = await c.get("/")
            assert r.status_code == 200 and "Brigade" in r.text and "text/html" in r.headers["content-type"]

            h = (await c.get("/health")).json()
            assert h["has_key"] is False and h["verify_policy"] in ("strategic", "full")

            # claude engine without a key -> clear 409, not a silent fallback
            r = await c.post("/jobs", json={"problem": "x", "demo": False})
            assert r.status_code == 409 and "API key" in r.json()["detail"]

            # demo engine always works and is labeled as such
            r = await c.post("/jobs", json={"problem": DEMO_PROBLEM, "demo": True})
            assert r.status_code == 200 and r.json()["engine"] == "demo"
            job_id = r.json()["job_id"]
            for _ in range(500):
                body = (await c.get(f"/jobs/{job_id}")).json()
                if body["status"] not in ("queued", "running"):
                    break
                await asyncio.sleep(0.01)
            assert body["status"] == "proved" and body["engine"] == "demo"

            # paste a key -> has_key flips (no remember: nothing written to disk)
            r = await c.post("/settings", json={"api_key": "sk-ant-test", "remember": False})
            assert r.json() == {"has_key": True, "saved_to": None}
            assert (await c.get("/health")).json()["has_key"] is True


async def test_replay_engine_refuses_custom_input():
    """Honesty guard: the fixed replay may never masquerade as proving a user's claim."""
    cfg = demo_config()
    cfg.fake_llm = False
    cfg.anthropic_api_key = ""
    app = create_app(cfg, llm=None, lean=default_fake_lean())
    async with app.router.lifespan_context(app):
        async with await _client(app) as c:
            r = await c.post("/jobs", json={"problem": "1+1=3", "demo": True})
            assert r.status_code == 409
            assert "does not" in r.json()["detail"] and "recorded" in r.json()["detail"]
            # the fixed scenario itself still runs
            r = await c.post("/jobs", json={"problem": DEMO_PROBLEM, "demo": True})
            assert r.status_code == 200
            # and the served UI carries the honest labeling
            html = (await c.get("/")).text
            assert "ignores your text" in html and "Recorded scenario" in html
