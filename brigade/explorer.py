"""Frontier exploration sweeps and persistent Ramsey Theory research lab notebook."""

from __future__ import annotations

from datetime import datetime, timezone
import json
from pathlib import Path
from typing import Any

from . import density_hj, hypergraph, skeptic_hj


def explore_family(
    family: str,
    *,
    k: int = 3,
    r: int = 2,
    s: int = 3,
    t: int | None = None,
    start: int = 1,
    stop: int = 8,
    max_nodes: int = 120_000,
) -> list[dict[str, Any]]:
    """Sweep a Ramsey Theory parameter frontier and return structured findings + coloring metadata."""
    fam = family.lower().strip()
    rows: list[dict[str, Any]] = []
    if stop < start:
        return rows

    if fam == "hj":
        for d in range(max(1, start), stop + 1):
            if k**d > 729 and d > start + 2:
                rows.append({"family": "hj", "d": d, "k": k, "r": r, "status": "SKIPPED_LARGE"})
                continue
            res = skeptic_hj.solve_hj(d, k, r, max_nodes=max_nodes, time_limit_s=5.0)
            entry: dict[str, Any] = {
                "family": "hj",
                "d": d,
                "k": k,
                "r": r,
                "status": res.status,
                "nodes": res.nodes_explored,
            }
            if res.witness_coloring is not None:
                entry["structure"] = hypergraph.analyze_coloring_structure(res.witness_coloring)
            rows.append(entry)
        return rows

    if fam == "vdw":
        for n in range(max(1, start), stop + 1):
            res = hypergraph.solve_vdw_cert(n, k, r, max_nodes=max_nodes, walksat_steps=5000)
            entry = {
                "family": "vdw",
                "N": n,
                "k": k,
                "r": r,
                "status": res.status,
                "nodes": res.nodes_explored,
                "edges": res.edge_count,
            }
            if res.witness_coloring is not None:
                entry["structure"] = res.structure
                entry["witness"] = res.witness_coloring
            rows.append(entry)
        return rows

    if fam == "schur":
        for n in range(max(1, start), stop + 1):
            res = hypergraph.solve_schur(n, r, max_nodes=max_nodes, walksat_steps=5000)
            entry = {
                "family": "schur",
                "N": n,
                "r": r,
                "status": res.status,
                "nodes": res.nodes_explored,
                "edges": res.edge_count,
            }
            if res.witness_coloring is not None:
                entry["structure"] = res.structure
                entry["witness"] = res.witness_coloring
            rows.append(entry)
        return rows

    if fam == "ramsey":
        for n in range(max(2, start), stop + 1):
            res = hypergraph.solve_graph_ramsey(n, s, t, r=r, steps=8000)
            rows.append(
                {
                    "family": "ramsey",
                    "N": n,
                    "s": s,
                    "t": t,
                    "r": r,
                    "status": res.status,
                    "notes": res.notes,
                }
            )
        return rows

    if fam == "dhj":
        for d in range(max(1, start), stop + 1):
            if k**d > 729:
                rows.append({"family": "dhj", "d": d, "k": k, "status": "SKIPPED_LARGE"})
                continue
            dres = density_hj.solve_dhj(d, k, restarts=15, steps=600)
            rows.append(
                {
                    "family": "dhj",
                    "d": d,
                    "k": k,
                    "size": dres.size,
                    "num_words": dres.num_words,
                    "optimal": dres.optimal,
                }
            )
        return rows

    if fam == "moser":
        for d in range(max(1, start), stop + 1):
            if 3**d > 729:
                rows.append({"family": "moser", "d": d, "k": 3, "status": "SKIPPED_LARGE"})
                continue
            mres = density_hj.solve_moser(d)
            rows.append(
                {
                    "family": "moser",
                    "d": d,
                    "k": 3,
                    "size": mres.size,
                    "num_words": mres.num_words,
                    "optimal": mres.optimal,
                }
            )
        return rows

    raise ValueError(f"Unsupported exploration family: {family!r}. Choose from hj, vdw, schur, ramsey, dhj, moser.")


class ResearchLab:
    """Manages persistent discovery tracking under `research/notes.jsonl` and `research/DISCOVERIES.md`."""

    def __init__(self, project_dir: Path | str):
        self.project_dir = Path(project_dir).resolve()
        self.research_dir = self.project_dir / "research"
        self.notes_path = self.research_dir / "notes.jsonl"
        self.markdown_path = self.research_dir / "DISCOVERIES.md"

    def list_notes(self, family: str | None = None) -> list[dict[str, Any]]:
        if not self.notes_path.exists():
            return []
        notes: list[dict[str, Any]] = []
        for line in self.notes_path.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if not line:
                continue
            item = json.loads(line)
            if family is None or item.get("family", "").lower() == family.lower():
                notes.append(item)
        return notes

    def add_note(
        self,
        *,
        title: str,
        family: str,
        status: str,
        summary: str,
        theorem: str = "",
        evidence: str = "",
    ) -> dict[str, Any]:
        """Append a dated research note and re-render `research/DISCOVERIES.md`."""
        self.research_dir.mkdir(parents=True, exist_ok=True)
        existing = self.list_notes()
        note = {
            "id": len(existing) + 1,
            "timestamp": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "title": title.strip(),
            "family": family.strip().lower(),
            "status": status.strip(),
            "summary": summary.strip(),
            "theorem": theorem.strip(),
            "evidence": evidence.strip(),
        }
        existing.append(note)
        self.notes_path.write_text(
            "".join(json.dumps(n, ensure_ascii=False) + "\n" for n in existing),
            encoding="utf-8",
        )
        self.render_markdown(existing)
        return note

    def render_markdown(self, notes: list[dict[str, Any]] | None = None) -> Path:
        """Render clean markdown dashboard `research/DISCOVERIES.md`."""
        self.research_dir.mkdir(parents=True, exist_ok=True)
        items = notes if notes is not None else self.list_notes()
        lines = [
            "# Ramsey Theory Research Discoveries & Frontier Log",
            "",
            "Tracked by `brigade lab` and `brigade_lab_note` (MCP). Every theorem marked `VERIFIED`",
            "is compiled in Lean 4 with zero `sorry` and audited via `#print axioms`.",
            "",
            "| # | Family | Status | Title | Theorem | Summary |",
            "| --- | --- | --- | --- | --- | --- |",
        ]
        for item in items:
            thm = f"`{item['theorem']}`" if item.get("theorem") else "—"
            lines.append(
                f"| {item['id']} | `{item['family']}` | **{item['status']}** | "
                f"{item['title']} | {thm} | {item['summary']} |"
            )
        lines.append("")
        self.markdown_path.write_text("\n".join(lines), encoding="utf-8")
        return self.markdown_path
