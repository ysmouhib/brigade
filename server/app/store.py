"""Job store. In-memory by default; set BRIGADE_DB=<path> to also persist finished jobs
to SQLite so they survive restarts (running jobs still die with the process)."""
from __future__ import annotations
import asyncio
import sqlite3
from typing import Optional

from .models import Job


class Store:
    def __init__(self, db_path: str = ""):
        self.jobs: dict[str, Job] = {}
        self.tasks: dict[str, asyncio.Task] = {}
        self._db: sqlite3.Connection | None = None
        if db_path:
            self._db = sqlite3.connect(db_path)
            self._db.execute("CREATE TABLE IF NOT EXISTS jobs "
                             "(id TEXT PRIMARY KEY, created_at REAL, data TEXT)")
            self._db.commit()
            for (data,) in self._db.execute("SELECT data FROM jobs"):
                try:
                    job = Job.model_validate_json(data)
                    self.jobs[job.id] = job
                except Exception:  # noqa: BLE001 — a corrupt row must not block boot
                    continue

    def add(self, job: Job, task: asyncio.Task) -> None:
        self.jobs[job.id] = job
        self.tasks[job.id] = task
        task.add_done_callback(lambda _t, jid=job.id: self.persist(jid))

    def persist(self, job_id: str) -> None:
        job = self.jobs.get(job_id)
        if self._db is None or job is None:
            return
        try:
            self._db.execute("INSERT OR REPLACE INTO jobs VALUES (?, ?, ?)",
                             (job.id, job.created_at, job.model_dump_json()))
            self._db.commit()
        except sqlite3.Error:
            pass  # persistence is best-effort; the in-memory job stays authoritative

    def get(self, job_id: str) -> Optional[Job]:
        return self.jobs.get(job_id)

    def cancel(self, job_id: str) -> bool:
        t = self.tasks.get(job_id)
        if t and not t.done():
            t.cancel()
            return True
        return False

    async def shutdown(self) -> None:
        for t in self.tasks.values():
            if not t.done():
                t.cancel()
        await asyncio.gather(*self.tasks.values(), return_exceptions=True)
        if self._db is not None:
            self._db.close()
