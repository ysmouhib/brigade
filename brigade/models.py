"""Typed data models for the Hales-Jewett proving brigade and persistent ledger."""

from __future__ import annotations

from dataclasses import asdict, dataclass, field
from enum import Enum
from typing import Any
import uuid


def new_id(prefix: str = "n") -> str:
    return f"{prefix}_{uuid.uuid4().hex[:8]}"


class JobStatus(str, Enum):
    PENDING = "pending"
    RUNNING = "running"
    PROVED = "proved"
    REFUTED = "refuted"
    EXHAUSTED = "exhausted"
    ERROR = "error"


class NodeStatus(str, Enum):
    PLANNED = "planned"
    STATEMENT_OK = "statement_ok"
    PROVING = "proving"
    VERIFIED = "verified"
    REFUTED = "refuted"
    STUCK = "stuck"


@dataclass
class VerifyResult:
    ok: bool
    errors: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)
    sorries: int = 0
    goals: list[str] = field(default_factory=list)
    raw_output: str = ""
    elapsed_s: float = 0.0

    def summary(self) -> str:
        if self.ok and self.sorries == 0:
            return f"OK (0 errors, 0 sorries, {self.elapsed_s:.2f}s)"
        if self.ok:
            return f"OK with {self.sorries} sorry(ies)"
        return "; ".join(self.errors[:3]) or "unknown Lean error"


@dataclass
class AuditResult:
    ok: bool
    theorem_name: str
    axioms: list[str] = field(default_factory=list)
    note: str = ""


@dataclass
class Refutation:
    claim: str
    counterexample: dict[str, Any] = field(default_factory=dict)
    lean_witness_code: str = ""
    lean_verified: bool = False
    note: str = ""


@dataclass
class HJSearchResult:
    d: int
    k: int
    r: int
    status: str  # "SAT_LINE_FREE" | "UNSAT_MONO_FORCED" | "UNKNOWN"
    num_words: int
    num_lines: int
    nodes_explored: int
    elapsed_s: float
    witness_coloring: list[int] | None = None
    cert_tree: Any = None
    root_sym_idx: int | None = None


@dataclass
class ProofNode:
    id: str = field(default_factory=lambda: new_id("node"))
    kind: str = "lemma"  # "theorem" | "lemma"
    lean_name: str = ""
    informal: str = ""
    sketch: str = ""
    lean_statement: str = ""
    lean_proof: str = ""
    goal: str = ""
    status: NodeStatus = NodeStatus.PLANNED
    parent_id: str | None = None
    depth: int = 0
    attempts: int = 0
    last_errors: list[str] = field(default_factory=list)
    decomposed: bool = False
    probed: bool = False
    imports: list[str] = field(default_factory=lambda: ["HJBrigade"])

    def to_dict(self) -> dict[str, Any]:
        d = asdict(self)
        d["status"] = self.status.value
        return d

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> ProofNode:
        copy = dict(data)
        copy["status"] = NodeStatus(copy["status"])
        return cls(**copy)


@dataclass
class AgentEvent:
    seq: int
    level: str
    agent: str
    type: str
    content: str
    node_id: str | None = None


@dataclass
class Job:
    problem: str
    id: str = field(default_factory=lambda: new_id("job"))
    status: JobStatus = JobStatus.PENDING
    phase: str = "init"
    round: int = 0
    llm_calls: int = 0
    lean_calls: int = 0
    root_id: str | None = None
    nodes: dict[str, ProofNode] = field(default_factory=dict)
    events: list[AgentEvent] = field(default_factory=list)
    refutation: Refutation | None = None
    final_lean: str = ""
    summary: str = ""

    def root(self) -> ProofNode:
        assert self.root_id is not None and self.root_id in self.nodes
        return self.nodes[self.root_id]

    def children(self, node_id: str) -> list[ProofNode]:
        return [n for n in self.nodes.values() if n.parent_id == node_id]


@dataclass
class PremiseEntry:
    module: str
    kind: str
    name: str
    signature: str
    line: int
    doc: str = ""
