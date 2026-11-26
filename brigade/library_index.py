"""Premise index over `HJBrigade/**/*.lean` and persistent proof DAG ledger."""

from __future__ import annotations

import json
from pathlib import Path
import re

from .models import NodeStatus, PremiseEntry, ProofNode

_DECL_RE = re.compile(
    r"^(theorem|lemma|def|abbrev|structure|inductive|class)\s+([A-Za-z_][A-Za-z0-9_.']*)\b(.*)$"
)
_TOKEN_RE = re.compile(r"[A-Za-z0-9_']+")


class PremiseIndex:
    """Indexes compiled declarations in `HJBrigade` so LLM agents cite real names."""

    def __init__(self, project_dir: Path | str):
        self.project_dir = Path(project_dir).resolve()
        self.entries: list[PremiseEntry] = []
        self.refresh()

    def refresh(self) -> None:
        self.entries.clear()
        lib_dir = self.project_dir / "HJBrigade"
        if not lib_dir.exists():
            return
        for path in sorted(lib_dir.rglob("*.lean")):
            rel = path.relative_to(self.project_dir).with_suffix("")
            module = ".".join(rel.parts)
            lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
            pending_doc = ""
            i = 0
            while i < len(lines):
                stripped = lines[i].strip()
                if stripped.startswith("/--"):
                    doc_lines = [stripped]
                    while not doc_lines[-1].endswith("-/") and i + 1 < len(lines):
                        i += 1
                        doc_lines.append(lines[i].strip())
                    pending_doc = " ".join(doc_lines).strip("/- ")
                    i += 1
                    continue
                m = _DECL_RE.match(stripped)
                if m:
                    kind, name, rest = m.group(1), m.group(2), m.group(3)
                    sig_parts = [f"{kind} {name}{rest}"]
                    j = i
                    while j + 1 < len(lines):
                        if ":=" in sig_parts[-1] or "where" in sig_parts[-1]:
                            break
                        nxt = lines[j + 1].strip()
                        if not nxt or nxt.startswith(("--", "theorem ", "lemma ", "def ", "end ")):
                            break
                        j += 1
                        sig_parts.append(nxt)
                    sig = " ".join(sig_parts).split(":=")[0].strip()
                    self.entries.append(
                        PremiseEntry(
                            module=module,
                            kind=kind,
                            name=name,
                            signature=sig,
                            line=i + 1,
                            doc=pending_doc[:200],
                        )
                    )
                    pending_doc = ""
                elif stripped and not stripped.startswith("--"):
                    pending_doc = ""
                i += 1

    def search(self, query: str, limit: int = 12) -> list[PremiseEntry]:
        q_tokens = {t.lower() for t in _TOKEN_RE.findall(query) if len(t) >= 2}
        if not q_tokens:
            return self.entries[:limit]
        scored: list[tuple[int, PremiseEntry]] = []
        for entry in self.entries:
            hay = f"{entry.name} {entry.signature} {entry.doc} {entry.module}".lower()
            score = 0
            for tok in q_tokens:
                if tok in entry.name.lower():
                    score += 4
                elif tok in hay:
                    score += 1
            if entry.kind in ("theorem", "lemma"):
                score += 1
            if score > 0:
                scored.append((score, entry))
        scored.sort(key=lambda pair: (-pair[0], pair[1].module, pair[1].line))
        return [e for _, e in scored[:limit]]

    def format_hints(self, query: str, limit: int = 10) -> list[str]:
        hits = self.search(query, limit=limit)
        return [f"[{e.module}] {e.signature}" for e in hits]


class ProofLedger:
    """Persistent JSON DAG of Lean-verified lemmas that survives across rounds and runs."""

    def __init__(self, path: Path | str):
        self.path = Path(path)
        self.nodes: dict[str, ProofNode] = {}
        self.load()

    def load(self) -> None:
        if not self.path.exists():
            return
        try:
            raw = json.loads(self.path.read_text(encoding="utf-8"))
            self.nodes = {
                k: ProofNode.from_dict(v)
                for k, v in raw.get("nodes", {}).items()
            }
        except (OSError, json.JSONDecodeError, KeyError, ValueError):
            self.nodes = {}

    def save(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        payload = {
            "version": 1,
            "nodes": {k: v.to_dict() for k, v in self.nodes.items()},
        }
        self.path.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    def add_verified(self, node: ProofNode) -> None:
        if node.status != NodeStatus.VERIFIED:
            raise ValueError("Invariant I1: ProofLedger only persists VERIFIED nodes")
        key = node.lean_name or node.id
        self.nodes[key] = node
        self.save()

    def get_verified(self) -> list[ProofNode]:
        return [n for n in self.nodes.values() if n.status == NodeStatus.VERIFIED]

    def find_matching_statement(self, statement: str) -> ProofNode | None:
        norm = " ".join(statement.split())
        for n in self.nodes.values():
            if n.status == NodeStatus.VERIFIED and " ".join(n.lean_statement.split()) == norm:
                return n
        return None
