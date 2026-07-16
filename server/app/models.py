"""Pydantic data models shared by the orchestrator, the API, and the web UI."""
from __future__ import annotations
import time
import uuid
from enum import Enum
from typing import Optional
from pydantic import BaseModel, Field


def new_id(prefix: str) -> str:
    return f"{prefix}_{uuid.uuid4().hex[:8]}"


class NodeStatus(str, Enum):
    CONJECTURED = "conjectured"      # informal statement exists
    STATEMENT_OK = "statement_ok"    # Lean accepts `statement := by sorry`
    PROVING = "proving"              # a worker is on it
    VERIFIED = "verified"            # Lean accepts a sorry-free proof
    REFUTED = "refuted"              # counterexample found
    STUCK = "stuck"                  # budget exhausted on this node
    ABANDONED = "abandoned"          # dropped during replanning


class JobStatus(str, Enum):
    QUEUED = "queued"
    RUNNING = "running"
    PROVED = "proved"
    REFUTED = "refuted"
    EXHAUSTED = "exhausted"          # budgets spent, partial results reported
    CANCELLED = "cancelled"
    ERROR = "error"


class ProofNode(BaseModel):
    id: str = Field(default_factory=lambda: new_id("n"))
    parent_id: Optional[str] = None
    depth: int = 0
    kind: str = "lemma"              # "theorem" for the root
    informal: str = ""
    sketch: str = ""
    lean_name: str = ""
    lean_statement: str = ""         # pinned after the statement gate; never edited by provers
    goal: str = ""                   # Lean goal state from the statement gate (REPL backend)
    lean_proof: str = ""             # tactic block, set only after verification
    status: NodeStatus = NodeStatus.CONJECTURED
    attempts: int = 0
    decomposed: bool = False
    probed: bool = False
    last_errors: list[str] = Field(default_factory=list)


class AgentEvent(BaseModel):
    seq: int
    ts: float = Field(default_factory=time.time)
    level: str = "worker"            # chef | sous | worker | lean | system
    agent: str = ""
    type: str = ""                   # e.g. brainstorm, plan, formalize, prove_attempt, lean_check, repair, ...
    content: str = ""
    node_id: Optional[str] = None


class Refutation(BaseModel):
    counterexample: dict[str, int]
    claim_expr: str
    note: str = ""


class Budgets(BaseModel):
    max_rounds: Optional[int] = None
    repair_cycles: Optional[int] = None
    max_depth: Optional[int] = None
    n_brainstormers: Optional[int] = None


class Job(BaseModel):
    id: str = Field(default_factory=lambda: new_id("job"))
    problem: str
    status: JobStatus = JobStatus.QUEUED
    phase: str = "queued"
    round: int = 0
    created_at: float = Field(default_factory=time.time)
    root_id: Optional[str] = None
    nodes: dict[str, ProofNode] = Field(default_factory=dict)
    events: list[AgentEvent] = Field(default_factory=list)
    final_lean: str = ""
    refutation: Optional[Refutation] = None
    summary: str = ""
    llm_calls: int = 0
    lean_calls: int = 0
    engine: str = "claude"        # claude | demo

    # ---- helpers ----
    def children(self, node_id: str) -> list[ProofNode]:
        return [n for n in self.nodes.values() if n.parent_id == node_id]

    def root(self) -> ProofNode:
        assert self.root_id
        return self.nodes[self.root_id]


class NewJobRequest(BaseModel):
    problem: str
    budgets: Optional[Budgets] = None
    demo: bool = False                      # run on the offline demo engine
    verify_policy: Optional[str] = None     # 'full' | 'strategic'
