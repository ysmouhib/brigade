"""Coordinator control loop enforcing invariants I1-I4, HJ/VdW/DHJ skeptic certificates, and persistent ledger."""

from __future__ import annotations

import asyncio
from dataclasses import dataclass
from pathlib import Path
import re
import textwrap
import traceback

from . import agents, hypergraph, skeptic_hj
from .lean_verifier import RealLeanVerifier, lint_proof
from .library_index import PremiseIndex, ProofLedger
from .llm import LLM, LLMError
from .models import AgentEvent, Job, JobStatus, NodeStatus, ProofNode, Refutation

_NAME_RE = re.compile(r"[^A-Za-z0-9_']")
_HJ_PATTERN_RE = re.compile(
    r"(?:(¬|not)\s*)?HJUpper\s+(\d+)\s+(\d+)\s+(\d+)",
    re.IGNORECASE,
)
_VDW_PATTERN_RE = re.compile(
    r"(?:(¬|not)\s*)?HasMonoAP\s+(\d+)\s+(\d+)\s+(\d+)",
    re.IGNORECASE,
)
_SCHUR_PATTERN_RE = re.compile(
    r"(?:(¬|not)\s*)?HasMonoSchur\s+(\d+)\s+(\d+)",
    re.IGNORECASE,
)
_RAMSEY_PATTERN_RE = re.compile(
    r"(?:(¬|not)\s*)?GraphRamseyUpper\s+(\d+)\s+(\d+)\s+(\d+)",
    re.IGNORECASE,
)
_MRAMSEY_PATTERN_RE = re.compile(
    r"(?:(¬|not)\s*)?MulticolorRamseyUpper\s+(\d+)\s+(\d+)\s+(\d+)",
    re.IGNORECASE,
)
_PROVE_PREFIX_RE = re.compile(r"^(?:prove(?:\s+that)?|show(?:\s+that)?)\s+", re.IGNORECASE)

CASCADE_BODIES = [
    "decide",
    "omega",
    "simp",
    "first\n  | decide\n  | omega\n  | simp",
    "exact hj_one_color _",
    "exact hj_alphabet_one _ (by omega)",
    "exact hj_two_upper _",
    "exact hj_two_lower _",
    "exact hj_implies_vdw (hj_two_upper _)",
]

SHELAH_CASCADE_BODIES = [
    "exact hales_jewett_shelah _ _ (by omega) (by omega)",
    "exact hales_jewett _ _ (by omega) (by omega)",
    "exact van_der_waerden _ _ (by omega) (by omega)",
]


class BudgetExceeded(Exception):
    pass


@dataclass
class OrchestratorConfig:
    project_dir: Path
    max_rounds: int = 3
    max_llm_calls: int = 40
    max_lean_calls: int = 60
    n_brainstormers: int = 3
    statement_retries: int = 3
    repair_cycles: int = 3
    max_depth: int = 2
    prove_samples: int = 2
    verify_policy: str = "strategic"  # "strategic" | "full"
    tactic_cascade: bool = True
    enable_skeptic: bool = True
    ledger_path: Path | None = None
    skeptic_max_nodes: int = 250_000
    skeptic_time_limit_s: float = 15.0


class Orchestrator:
    def __init__(
        self,
        job: Job,
        llm: LLM,
        verifier: RealLeanVerifier,
        cfg: OrchestratorConfig,
    ):
        self.job = job
        self.llm = llm
        self.verifier = verifier
        self.cfg = cfg
        self._seq = 0
        self._names: set[str] = set()
        self.index = PremiseIndex(cfg.project_dir)
        ledger_file = cfg.ledger_path or (cfg.project_dir / ".brigade_ledger.json")
        self.ledger = ProofLedger(ledger_file)

    def emit(self, level: str, agent: str, type_: str, content: str, node_id: str | None = None) -> None:
        self._seq += 1
        self.job.events.append(
            AgentEvent(
                seq=self._seq,
                level=level,
                agent=agent,
                type=type_,
                content=content[:4000],
                node_id=node_id,
            )
        )

    async def _llm(self, coro):
        if self.job.llm_calls >= self.cfg.max_llm_calls:
            raise BudgetExceeded("LLM call budget exhausted")
        self.job.llm_calls += 1
        return await coro

    async def _check(self, code: str, node: ProofNode | None = None, context: str = ""):
        if self.job.lean_calls >= self.cfg.max_lean_calls:
            raise BudgetExceeded("Lean call budget exhausted")
        self.job.lean_calls += 1
        res = await self.verifier.check(code, context=context)
        self.emit("lean", "lean_verifier", "lean_check", res.summary(), node.id if node else None)
        return res

    async def _check_statement(self, header: str, node: ProofNode | None = None, context: str = ""):
        if self.job.lean_calls >= self.cfg.max_lean_calls:
            raise BudgetExceeded("Lean call budget exhausted")
        self.job.lean_calls += 1
        res = await self.verifier.check_statement(header, context=context)
        self.emit("lean", "lean_verifier", "statement_gate", res.summary(), node.id if node else None)
        return res

    def _unique_name(self, raw: str) -> str:
        base = _NAME_RE.sub("_", raw.strip()) or "lemma"
        if base[0].isdigit():
            base = "l_" + base
        name, idx = base, 1
        while name in self._names:
            idx += 1
            name = f"{base}_{idx}"
        self._names.add(name)
        return name

    @staticmethod
    def _theorem_text(node: ProofNode, body: str) -> str:
        indented = textwrap.indent(body.strip(), "  ")
        return f"{node.lean_statement.strip()} := by\n{indented}"

    def _verified_context(self, exclude_id: str | None = None) -> list[ProofNode]:
        seen_names: set[str] = set()
        out: list[ProofNode] = []
        for n in self.ledger.get_verified():
            if n.id != exclude_id and n.lean_name not in seen_names:
                seen_names.add(n.lean_name)
                out.append(n)
        for n in self.job.nodes.values():
            if n.status == NodeStatus.VERIFIED and n.id != exclude_id and n.lean_name not in seen_names:
                seen_names.add(n.lean_name)
                out.append(n)
        return out

    def _context_code(self, exclude_id: str | None = None) -> str:
        return "\n\n".join(self._theorem_text(h, h.lean_proof) for h in self._verified_context(exclude_id))

    def _clean_body(self, raw: str) -> str:
        """Enforce I3: strip any echoed `theorem/lemma ... := by` header."""
        body = raw.strip()
        body = re.sub(r"^```(?:lean4?|lean)?\s*|\s*```$", "", body).strip()
        if body.startswith(("theorem ", "lemma ")):
            m = re.search(r":=\s*by\b", body)
            body = body[m.end() :].strip() if m else body
        if body.startswith("by\n") or body == "by":
            body = body[2:].strip()
        elif body.startswith("by "):
            body = body[3:].strip()
        return textwrap.dedent(body)

    def _add_node(
        self,
        informal: str,
        sketch: str,
        parent: ProofNode | None,
        kind: str = "lemma",
        name_hint: str = "",
    ) -> ProofNode:
        node = ProofNode(
            kind=kind,
            informal=informal,
            sketch=sketch,
            parent_id=parent.id if parent else None,
            depth=(parent.depth + 1) if parent else 0,
        )
        node.lean_name = self._unique_name(
            name_hint or ("thm_main" if kind == "theorem" else f"lemma_{len(self.job.nodes)}")
        )
        self.job.nodes[node.id] = node
        return node

    def _mark_verified(self, node: ProofNode, body: str, msg: str) -> None:
        node.lean_proof = body
        node.status = NodeStatus.VERIFIED
        node.last_errors = []
        self.ledger.add_verified(node)
        self.emit("chef", "chef", "verified", msg, node.id)

    async def _try_symbolic_fastpath(self) -> bool:
        """Try closing direct formal claims (`HJUpper`, `MHJUpper`, `HasMonoAP`, `GraphRamseyUpper`, `HasMonoSchur`, `IsLineFree`)."""
        candidate = _PROVE_PREFIX_RE.sub("", self.job.problem.strip()).rstrip(".")
        if not any(
            tok in candidate
            for tok in (
                "HJUpper",
                "MHJUpper",
                "HasMonoAP",
                "HasMonoSchur",
                "GraphRamseyUpper",
                "MulticolorRamseyUpper",
                "erdosSzekeresBound",
                "shelahHJDim",
                "mhjDim",
                "IsGeomLineFree",
                "IsLineFree",
                "wordCard",
            )
        ):
            return False
        thm_name = self._unique_name("thm_main")
        header = f"theorem {thm_name} : {candidate}"
        gate = await self._check_statement(header)
        if not gate.ok:
            return False
        if "GraphRamseyUpper" in candidate:
            symbolic_bodies = [
                "exact erdos_szekeres _ _ (by omega) (by omega)",
                "exact graph_ramsey _ _ (by omega) (by omega)",
                "exact ramsey_left_one _ _ (by omega)",
                "exact ramsey_right_one _ _ (by omega)",
                "exact ramsey_left_two _ (by omega)",
                "exact ramsey_right_two _ (by omega)",
                "exact ramsey_3_3_upper",
                "exact ramsey_3_3_lower",
                "exact ramsey_3_4_upper",
                "exact ramsey_3_4_lower",
                "exact ramsey_3_5_upper",
                "exact ramsey_3_5_lower",
                "exact ramsey_4_4_upper",
                "exact ramsey_4_4_lower",
                "exact ramsey_3_4_upper.symm",
                "exact ramsey_3_5_upper.symm",
            ]
        elif "MulticolorRamseyUpper" in candidate:
            symbolic_bodies = [
                "exact multicolor_triangle_ramsey _ (by omega)",
                "exact ramsey_multicolor_triangles _ (by omega)",
                "exact ramsey_3_3_multicolor_upper",
                "exact ramsey_3_3_3_upper",
                "exact ramsey_3_3_3_lower",
            ]
        elif "HasMonoSchur" in candidate:
            symbolic_bodies = [
                "exact schur_theorem _ (by omega)",
                "exact schur_1_gt_1",
                "exact schur_1_le_2",
                "exact schur_2_gt_4",
                "exact schur_2_le_5",
                "exact schur_3_gt_13",
                "exact schur_3_le_14",
            ]
        elif "mhjDim" in candidate or "MHJUpper" in candidate:
            symbolic_bodies = [
                "exact mhj_shelah _ _ _ (by omega) (by omega)",
                "exact multidimensional_hales_jewett _ _ _ (by omega) (by omega) (by omega)",
            ]
        elif "shelahHJDim" in candidate or "∃ d" in candidate or "∃ N" in candidate:
            symbolic_bodies = list(SHELAH_CASCADE_BODIES)
        elif "IsGeomLineFree" in candidate:
            symbolic_bodies = [
                "exact moser_1_3_upper",
                "exact moser_2_3_upper",
                "exact moser_3_3_upper",
                "exact moser_4_3_upper_48",
            ]
        elif "IsLineFree" in candidate or "wordCard" in candidate:
            symbolic_bodies = [
                "exact sperner_dhj_two _",
                "exact c_1_3_upper",
                "exact c_2_3_upper",
                "exact c_3_3_upper",
                "exact c_4_3_upper",
                "exact c_5_3_upper",
                "exact c_6_3_upper",
            ]
        else:
            symbolic_bodies = [
                "exact hj_one_color _",
                "exact hj_alphabet_one _ (by omega)",
                "exact hj_two_upper _",
                "exact hj_two_lower _",
                "exact hj_implies_vdw (hj_two_upper _)",
            ]
        for body in symbolic_bodies:
            code = f"{header} := by\n  {body}"
            chk = await self._check(code)
            if chk.ok and chk.sorries == 0:
                audit = await self.verifier.axiom_audit(code, thm_name)
                self.emit("lean", "lean_verifier", "axiom_audit", f"ok={audit.ok} axioms={audit.axioms}")
                if audit.ok:
                    self.job.final_lean = code
                    self.job.status = JobStatus.PROVED
                    self.job.phase = "proved"
                    self.job.summary = f"PROVED {thm_name} directly via HJBrigade theorem cascade (0 LLM calls)."
                    self.emit("chef", "chef", "proved", self.job.summary)
                    return True
        return False

    async def _try_vdw_skeptic(self, N: int, k: int, r: int, asserts_upper: bool) -> bool:
        if N < 1 or k < 1 or r < 1 or N > 40:
            return False
        self.emit("worker", "skeptic", "vdw_solve", f"Solving finite HasMonoAP {N} {k} {r}...")
        res = hypergraph.solve_vdw_cert(
            N, k, r, root=N // 2, max_nodes=self.cfg.skeptic_max_nodes, walksat_steps=8000
        )
        if res.status == "UNKNOWN":
            return False
        if res.status == "SAT_FREE" and res.witness_coloring is not None:
            thm_name = self._unique_name(f"vdw_{k}_{r}_gt_{N}")
            lean_code = hypergraph.emit_vdw_cert_lean(res, theorem_name=thm_name)
            chk = await self._check(lean_code)
            audit = await self.verifier.axiom_audit(lean_code, thm_name)
            self.emit("lean", "lean_verifier", "axiom_audit", f"ok={audit.ok} axioms={audit.axioms}")
            if not (chk.ok and chk.sorries == 0 and audit.ok):
                return False
            if asserts_upper:
                self.job.refutation = Refutation(
                    claim=self.job.problem,
                    counterexample={"N": N, "k": k, "r": r, "coloring": res.witness_coloring},
                    lean_witness_code=lean_code,
                    lean_verified=True,
                    note=f"AP-free {r}-coloring of Fin {N} verified by Lean 4.",
                )
                self.job.final_lean = lean_code
                self.job.status = JobStatus.REFUTED
                self.job.phase = "refuted"
                self.job.summary = f"REFUTED with Lean-verified AP-free coloring {thm_name}."
                self.emit("chef", "chef", "refuted", self.job.summary)
                return True
            self.job.final_lean = lean_code
            self.job.status = JobStatus.PROVED
            self.job.phase = "proved"
            self.job.summary = f"PROVED {thm_name} : ¬ HasMonoAP {N} {k} {r} via Lean-verified coloring."
            self.emit("chef", "chef", "proved", self.job.summary)
            return True

        thm_name = self._unique_name(f"vdw_{k}_{r}_le_{N}")
        lean_code = hypergraph.emit_vdw_cert_lean(res, theorem_name=thm_name)
        chk = await self._check(lean_code)
        audit = await self.verifier.axiom_audit(lean_code, thm_name)
        self.emit("lean", "lean_verifier", "axiom_audit", f"ok={audit.ok} axioms={audit.axioms}")
        if not (chk.ok and chk.sorries == 0 and audit.ok):
            return False
        if not asserts_upper:
            self.job.refutation = Refutation(
                claim=self.job.problem,
                counterexample={"N": N, "k": k, "r": r, "cert_nodes": res.nodes_explored},
                lean_witness_code=lean_code,
                lean_verified=True,
                note=f"HasMonoAP {N} {k} {r} proved true via kernel-checked HyperCert.",
            )
            self.job.final_lean = lean_code
            self.job.status = JobStatus.REFUTED
            self.job.phase = "refuted"
            self.job.summary = f"REFUTED claim ¬ HasMonoAP {N} {k} {r}; proved {thm_name}."
            self.emit("chef", "chef", "refuted", self.job.summary)
            return True
        self.job.final_lean = lean_code
        self.job.status = JobStatus.PROVED
        self.job.phase = "proved"
        self.job.summary = f"PROVED {thm_name} : HasMonoAP {N} {k} {r} via kernel-checked HyperCert."
        self.emit("chef", "chef", "proved", self.job.summary)
        return True

    async def _try_schur_skeptic(self, N: int, r: int, asserts_upper: bool) -> bool:
        if N < 1 or r < 1 or N > 20:
            return False
        self.emit("worker", "skeptic", "schur_solve", f"Solving finite HasMonoSchur {N} {r}...")
        res = hypergraph.solve_schur(N, r, max_nodes=self.cfg.skeptic_max_nodes, walksat_steps=6000)
        if res.status == "UNKNOWN":
            return False
        is_free = res.status == "SAT_FREE"
        thm_name = self._unique_name(f"schur_{r}_{'gt' if is_free else 'le'}_{N}")
        lean_code = hypergraph.emit_schur_lean(res, theorem_name=thm_name)
        chk = await self._check(lean_code)
        audit = await self.verifier.axiom_audit(lean_code, thm_name)
        self.emit("lean", "lean_verifier", "axiom_audit", f"ok={audit.ok} axioms={audit.axioms}")
        if not (chk.ok and chk.sorries == 0 and audit.ok):
            return False
        if (asserts_upper and is_free) or (not asserts_upper and not is_free):
            self.job.refutation = Refutation(
                claim=self.job.problem,
                counterexample={"N": N, "r": r, "status": res.status},
                lean_witness_code=lean_code,
                lean_verified=True,
                note=f"Schur finite claim resolved via {res.status} verified by Lean 4.",
            )
            self.job.final_lean = lean_code
            self.job.status = JobStatus.REFUTED
            self.job.phase = "refuted"
            self.job.summary = f"REFUTED claim using Lean-verified Schur certificate {thm_name}."
            self.emit("chef", "chef", "refuted", self.job.summary)
            return True
        self.job.final_lean = lean_code
        self.job.status = JobStatus.PROVED
        self.job.phase = "proved"
        self.job.summary = f"PROVED {thm_name} via Lean-verified Schur certificate."
        self.emit("chef", "chef", "proved", self.job.summary)
        return True

    async def _try_ramsey_skeptic(self, N: int, s: int, t: int | None, r: int, asserts_upper: bool) -> bool:
        if N < 2 or N > 18 or r < 1:
            return False
        self.emit("worker", "skeptic", "ramsey_solve", f"Searching clique-free coloring on Fin {N}...")
        res = hypergraph.solve_graph_ramsey(N, s, t, r=r, steps=10000)
        if res.status != "SAT_FREE":
            return False
        thm_name = self._unique_name(
            f"ramsey_{s}_{t}_{'gt'}_{N}" if (r == 2 and t is not None) else f"ramsey_mono_{r}_{s}_gt_{N}"
        )
        lean_code = hypergraph.emit_graph_ramsey_lower_lean(res, theorem_name=thm_name)
        chk = await self._check(lean_code)
        audit = await self.verifier.axiom_audit(lean_code, thm_name)
        self.emit("lean", "lean_verifier", "axiom_audit", f"ok={audit.ok} axioms={audit.axioms}")
        if not (chk.ok and chk.sorries == 0 and audit.ok):
            return False
        if asserts_upper:
            self.job.refutation = Refutation(
                claim=self.job.problem,
                counterexample={"N": N, "s": s, "t": t, "r": r, "notes": res.notes},
                lean_witness_code=lean_code,
                lean_verified=True,
                note=f"Clique-free coloring of Fin {N} verified by Lean 4.",
            )
            self.job.final_lean = lean_code
            self.job.status = JobStatus.REFUTED
            self.job.phase = "refuted"
            self.job.summary = f"REFUTED claim with Lean-verified graph witness {thm_name}."
            self.emit("chef", "chef", "refuted", self.job.summary)
            return True
        self.job.final_lean = lean_code
        self.job.status = JobStatus.PROVED
        self.job.phase = "proved"
        self.job.summary = f"PROVED {thm_name} via Lean-verified graph witness."
        self.emit("chef", "chef", "proved", self.job.summary)
        return True

    async def _try_hj_skeptic(self) -> bool:
        """Phase 0: Try symbolic base theorems, then finite combinatorial HJ/VdW/Schur/Ramsey solvers."""
        self.job.phase = "skeptic"
        if await self._try_symbolic_fastpath():
            return True

        m_vdw = _VDW_PATTERN_RE.search(self.job.problem)
        if m_vdw:
            if await self._try_vdw_skeptic(
                int(m_vdw.group(2)), int(m_vdw.group(3)), int(m_vdw.group(4)), m_vdw.group(1) is None
            ):
                return True

        m_schur = _SCHUR_PATTERN_RE.search(self.job.problem)
        if m_schur:
            if await self._try_schur_skeptic(
                int(m_schur.group(2)), int(m_schur.group(3)), m_schur.group(1) is None
            ):
                return True

        m_ram = _RAMSEY_PATTERN_RE.search(self.job.problem)
        if m_ram:
            if await self._try_ramsey_skeptic(
                int(m_ram.group(2)), int(m_ram.group(3)), int(m_ram.group(4)), 2, m_ram.group(1) is None
            ):
                return True

        m_mram = _MRAMSEY_PATTERN_RE.search(self.job.problem)
        if m_mram:
            if await self._try_ramsey_skeptic(
                int(m_mram.group(2)), int(m_mram.group(4)), None, int(m_mram.group(3)), m_mram.group(1) is None
            ):
                return True

        m = _HJ_PATTERN_RE.search(self.job.problem)
        d = k = r = None
        asserts_upper = True
        if m:
            asserts_upper = m.group(1) is None
            d, k, r = int(m.group(2)), int(m.group(3)), int(m.group(4))
        else:
            try:
                probe = await self._llm(agents.skeptic_hj_query(self.llm, self.job.problem))
                if probe.get("is_hj_finite_query"):
                    d, k, r = probe.get("d"), probe.get("k"), probe.get("r")
                    asserts_upper = bool(probe.get("claim_asserts_upper", True))
            except (LLMError, BudgetExceeded):
                return False

        if d is None or k is None or r is None:
            return False
        if d < 0 or k < 1 or r < 1 or k**d > 512:
            return False

        self.emit("worker", "skeptic", "hj_solve", f"Solving finite HJUpper {d} {k} {r}...")
        res = skeptic_hj.solve_hj(
            d, k, r, max_nodes=self.cfg.skeptic_max_nodes, time_limit_s=self.cfg.skeptic_time_limit_s
        )
        if res.status == "UNKNOWN":
            self.emit("worker", "skeptic", "hj_inconclusive", f"Solver budget reached ({res.nodes_explored} nodes)")
            return False

        if res.status == "SAT_LINE_FREE":
            thm_name = self._unique_name(f"hj_{k}_{r}_gt_{d}")
            lean_code = skeptic_hj.emit_lower_bound_lean(res, theorem_name=thm_name)
            chk = await self._check(lean_code)
            audit = await self.verifier.axiom_audit(lean_code, thm_name)
            self.emit("lean", "lean_verifier", "axiom_audit", f"ok={audit.ok} axioms={audit.axioms}")
            if not (chk.ok and chk.sorries == 0 and audit.ok):
                return False
            if asserts_upper:
                self.job.refutation = Refutation(
                    claim=self.job.problem,
                    counterexample={"d": d, "k": k, "r": r, "coloring_len": len(res.witness_coloring or [])},
                    lean_witness_code=lean_code,
                    lean_verified=True,
                    note=f"Line-free {r}-coloring of [{k}]^{d} verified by Lean 4.",
                )
                self.job.final_lean = lean_code
                self.job.status = JobStatus.REFUTED
                self.job.phase = "refuted"
                self.job.summary = f"REFUTED with Lean-verified counterexample {thm_name} (¬ HJUpper {d} {k} {r})."
                self.emit("chef", "chef", "refuted", self.job.summary)
                return True
            self.job.final_lean = lean_code
            self.job.status = JobStatus.PROVED
            self.job.phase = "proved"
            self.job.summary = f"PROVED {thm_name} : ¬ HJUpper {d} {k} {r} via Lean-verified coloring."
            self.emit("chef", "chef", "proved", self.job.summary)
            return True

        thm_name = self._unique_name(f"hj_{k}_{r}_le_{d}")
        lean_code = skeptic_hj.emit_upper_bound_lean(res, theorem_name=thm_name)
        chk = await self._check(lean_code)
        audit = await self.verifier.axiom_audit(lean_code, thm_name)
        self.emit("lean", "lean_verifier", "axiom_audit", f"ok={audit.ok} axioms={audit.axioms}")
        if not (chk.ok and chk.sorries == 0 and audit.ok):
            return False
        if not asserts_upper:
            self.job.refutation = Refutation(
                claim=self.job.problem,
                counterexample={"d": d, "k": k, "r": r, "cert_nodes": res.nodes_explored},
                lean_witness_code=lean_code,
                lean_verified=True,
                note=f"HJUpper {d} {k} {r} proved true via kernel-checked CertTree.",
            )
            self.job.final_lean = lean_code
            self.job.status = JobStatus.REFUTED
            self.job.phase = "refuted"
            self.job.summary = f"REFUTED claim ¬ HJUpper {d} {k} {r}; proved {thm_name}."
            self.emit("chef", "chef", "refuted", self.job.summary)
            return True
        self.job.final_lean = lean_code
        self.job.status = JobStatus.PROVED
        self.job.phase = "proved"
        self.job.summary = f"PROVED {thm_name} : HJUpper {d} {k} {r} via kernel-checked CertTree."
        self.emit("chef", "chef", "proved", self.job.summary)
        return True

    async def _probe_lemma_node(self, node: ProofNode) -> bool:
        """Per-lemma Skeptic pre-check: kill false planned lemmas before spending prover tokens.
        Returns True if the lemma was refuted (caller must abort the current subtree)."""
        if node.probed or node.kind != "lemma" or not node.lean_statement:
            return False
        node.probed = True

        if (m_hj := _HJ_PATTERN_RE.search(node.lean_statement)):
            asserts_upper = m_hj.group(1) is None
            d, k, r = int(m_hj.group(2)), int(m_hj.group(3)), int(m_hj.group(4))
            if d >= 0 and k >= 1 and r >= 1 and k**d <= 512:
                res = skeptic_hj.solve_hj(
                    d, k, r, max_nodes=self.cfg.skeptic_max_nodes, time_limit_s=self.cfg.skeptic_time_limit_s
                )
                if (asserts_upper and res.status == "SAT_LINE_FREE") or (
                    not asserts_upper and res.status == "UNSAT_MONO_FORCED"
                ):
                    node.status = NodeStatus.REFUTED
                    node.last_errors = [f"combinatorially refuted ({res.status})"]
                    self.emit(
                        "chef",
                        "chef",
                        "lemma_refuted",
                        f"{node.lean_name} refuted by HJ Skeptic ({res.status}) before proving.",
                        node.id,
                    )
                    return True

        if (m_vdw := _VDW_PATTERN_RE.search(node.lean_statement)):
            asserts_upper = m_vdw.group(1) is None
            N, k, r = int(m_vdw.group(2)), int(m_vdw.group(3)), int(m_vdw.group(4))
            if 1 <= N <= 40 and k >= 1 and r >= 1:
                vres = hypergraph.solve_vdw_cert(N, k, r, root=N // 2, max_nodes=self.cfg.skeptic_max_nodes)
                if (asserts_upper and vres.status == "SAT_FREE") or (
                    not asserts_upper and vres.status == "UNSAT_MONO"
                ):
                    node.status = NodeStatus.REFUTED
                    node.last_errors = [f"combinatorially refuted ({vres.status})"]
                    self.emit(
                        "chef",
                        "chef",
                        "lemma_refuted",
                        f"{node.lean_name} refuted by VdW Skeptic ({vres.status}) before proving.",
                        node.id,
                    )
                    return True

        if (m_schur := _SCHUR_PATTERN_RE.search(node.lean_statement)):
            asserts_upper = m_schur.group(1) is None
            N, r = int(m_schur.group(2)), int(m_schur.group(3))
            if 1 <= N <= 20 and r >= 1:
                sres = hypergraph.solve_schur(N, r, max_nodes=self.cfg.skeptic_max_nodes)
                if (asserts_upper and sres.status == "SAT_FREE") or (
                    not asserts_upper and sres.status == "UNSAT_MONO"
                ):
                    node.status = NodeStatus.REFUTED
                    node.last_errors = [f"combinatorially refuted ({sres.status})"]
                    self.emit(
                        "chef",
                        "chef",
                        "lemma_refuted",
                        f"{node.lean_name} refuted by Schur Skeptic ({sres.status}) before proving.",
                        node.id,
                    )
                    return True
        return False

    async def _try_cascade(self, node: ProofNode) -> bool:
        if not self.cfg.tactic_cascade or node.status != NodeStatus.STATEMENT_OK:
            return False
        ctx = self._context_code(node.id)
        bodies = (
            list(SHELAH_CASCADE_BODIES)
            if "shelahHJDim" in node.lean_statement
            else list(CASCADE_BODIES)
        )
        for body in bodies:
            if lint_proof(body):
                continue
            res = await self._check(self._theorem_text(node, body), node, context=ctx)
            if res.ok and res.sorries == 0:
                self._mark_verified(node, body, f"{node.lean_name} VERIFIED by tactic cascade (0 LLM calls).")
                return True
        return False

    async def run(self) -> None:
        self.job.status = JobStatus.RUNNING
        try:
            await self._run()
        except BudgetExceeded as e:
            self.job.status = JobStatus.EXHAUSTED
            self.job.phase = "exhausted"
            self.job.summary = f"Exhausted: {e}"
            self.emit("chef", "chef", "budget", str(e))
        except Exception:
            self.job.status = JobStatus.ERROR
            self.job.phase = "error"
            self.job.summary = traceback.format_exc()[-1000:]
            self.emit("system", "system", "error", self.job.summary)

    async def _run(self) -> None:
        self.emit("chef", "chef", "start", f"Problem received: {self.job.problem[:300]}")
        if self.cfg.enable_skeptic and await self._try_hj_skeptic():
            return

        feedback = ""
        for rnd in range(1, self.cfg.max_rounds + 1):
            self.job.round = rnd
            self.emit("chef", "chef", "round", f"=== Round {rnd}/{self.cfg.max_rounds} ===")

            self.job.phase = "brainstorm"
            personas = [p for _, p in agents.prompts.RAMSEY_PERSONAS[: max(1, self.cfg.n_brainstormers)]]
            results = await asyncio.gather(
                *[self._llm(agents.brainstorm(self.llm, self.job.problem, p, feedback)) for p in personas],
                return_exceptions=True,
            )
            strategies = []
            for r in results:
                if isinstance(r, Exception):
                    self.emit("worker", "brainstormer", "brainstorm_failed", str(r))
                elif isinstance(r, dict):
                    strategies.append(r)
            if not strategies:
                feedback = "All brainstormers failed."
                continue

            self.job.phase = "plan"
            plan = await self._llm(agents.strategize(self.llm, self.job.problem, strategies, feedback))
            root = self._add_node(
                plan.get("main_theorem_informal", self.job.problem),
                plan.get("assembly_note", ""),
                None,
                kind="theorem",
            )
            self.job.root_id = root.id
            lemmas = [
                self._add_node(sp.get("informal", ""), sp.get("sketch", ""), root)
                for sp in plan.get("lemmas", [])[:4]
            ]

            self.job.phase = "formalize"
            gate_ok = True
            for node in lemmas + [root]:
                if not await self._formalize_node(node):
                    gate_ok = False
            if not gate_ok or root.status != NodeStatus.STATEMENT_OK:
                feedback = self._failures("Formalization gate failed")
                continue

            self.job.phase = "prove"
            if await self._prove_subtree(root):
                self.job.phase = "assemble"
                final_code = self._assemble_final(root)
                chk = await self._check(final_code)
                lint = lint_proof(final_code)
                if chk.ok and chk.sorries == 0 and not lint:
                    audit = await self.verifier.axiom_audit(final_code, root.lean_name)
                    self.emit("lean", "lean_verifier", "axiom_audit", f"ok={audit.ok} axioms={audit.axioms}")
                    if audit.ok:
                        self.job.final_lean = final_code
                        self.job.status = JobStatus.PROVED
                        self.job.phase = "proved"
                        self.job.summary = (
                            f"PROVED {root.lean_name} in round {rnd} "
                            f"({self.job.lean_calls} Lean checks, {self.job.llm_calls} LLM calls)."
                        )
                        self.emit("chef", "chef", "proved", self.job.summary)
                        return
                    feedback = f"Axiom audit failed: {audit.note}"
                else:
                    feedback = f"Final assembly check failed: {lint or chk.errors[:2]}"
            else:
                feedback = self._failures("Proving failed")

        self.job.status = JobStatus.EXHAUSTED
        self.job.phase = "exhausted"
        verified_names = [n.lean_name for n in self._verified_context()]
        self.job.summary = f"Exhausted after {self.cfg.max_rounds} rounds. Verified lemmas preserved: {verified_names}"
        self.emit("chef", "chef", "exhausted", self.job.summary)

    async def _formalize_node(self, node: ProofNode) -> bool:
        if node.kind == "theorem":
            raw_cand = _PROVE_PREFIX_RE.sub("", self.job.problem.strip()).rstrip(".")
            if raw_cand and "\n" not in raw_cand and (
                any(sym in raw_cand for sym in ("→", "->", "∀", "∃", "∧", "∨", "≤", "<", "=", "¬"))
                or any(
                    tok in raw_cand
                    for tok in (
                        "HJUpper",
                        "MHJUpper",
                        "HasMonoAP",
                        "HasMonoSchur",
                        "GraphRamseyUpper",
                        "MulticolorRamseyUpper",
                        "IsLineFree",
                        "IsGeomLineFree",
                        "wordCard",
                    )
                )
            ):
                pinned_stmt = f"theorem {node.lean_name} : {raw_cand}"
                cached = self.ledger.find_matching_statement(pinned_stmt)
                if cached is not None:
                    node.lean_statement = pinned_stmt
                    self._mark_verified(node, cached.lean_proof, f"{node.lean_name} reused from persistent ProofLedger.")
                    return True
                gate = await self._check_statement(pinned_stmt, node, context=self._context_code(node.id))
                if gate.ok:
                    node.lean_statement = pinned_stmt
                    if gate.goals:
                        node.goal = gate.goals[0]
                    node.status = NodeStatus.STATEMENT_OK
                    self.emit("chef", "chef", "statement_pinned", f"{node.lean_name} pinned directly from formal problem", node.id)
                    return True

        errors: list[str] = []
        premises = self.index.format_hints(f"{node.informal} {node.sketch}", limit=10)
        for _ in range(self.cfg.statement_retries):
            try:
                out = await self._llm(agents.formalize(self.llm, node, self.job.problem, errors, premises))
            except LLMError as e:
                errors = [str(e)]
                continue
            stmt = out.get("lean_statement", "").strip()
            stmt = re.sub(r"^(theorem|lemma)\s+[A-Za-z0-9_']+", f"theorem {node.lean_name}", stmt)
            if not stmt.startswith("theorem"):
                stmt = f"theorem {node.lean_name} : {stmt}"
            node.lean_statement = stmt.split(":=")[0].strip()

            cached = self.ledger.find_matching_statement(node.lean_statement)
            if cached is not None:
                self._mark_verified(node, cached.lean_proof, f"{node.lean_name} reused from persistent ProofLedger.")
                return True

            self.emit("worker", "formalizer", "statement_attempt", node.lean_statement, node.id)
            res = await self._check_statement(node.lean_statement, node, context=self._context_code(node.id))
            if res.ok:
                if res.goals:
                    node.goal = res.goals[0]
                node.status = NodeStatus.STATEMENT_OK
                self.emit("worker", "formalizer", "statement_ok", f"{node.lean_name} elaborated", node.id)
                return True
            errors = res.errors
            node.last_errors = errors
        node.status = NodeStatus.STUCK
        return False

    async def _prove_subtree(self, node: ProofNode) -> bool:
        kids = [c for c in self.job.children(node.id) if c.status != NodeStatus.VERIFIED]
        if self.cfg.verify_policy == "strategic":
            for kid in kids:
                if await self._probe_lemma_node(kid):
                    node.status = NodeStatus.STUCK
                    return False
            if len(kids) >= 2:
                await self._strategic_batch(kids)
        for child in self.job.children(node.id):
            if child.status == NodeStatus.VERIFIED:
                continue
            if not await self._prove_subtree(child):
                node.status = NodeStatus.STUCK
                return False
        return await self._prove_node(node)

    async def _strategic_batch(self, kids: list[ProofNode]) -> None:
        cands: list[tuple[ProofNode, str]] = []
        for kid in kids:
            if kid.status != NodeStatus.STATEMENT_OK:
                continue
            if await self._try_cascade(kid):
                continue
            helpers = self._verified_context(kid.id)
            premises = self.index.format_hints(f"{kid.informal} {kid.lean_statement}", limit=8)
            try:
                out = await self._llm(agents.prove(self.llm, kid, helpers, [], "", premises))
            except LLMError as e:
                kid.last_errors = [str(e)]
                continue
            if out.get("claims_false"):
                continue
            body = self._clean_body(out.get("proof", ""))
            kid.attempts += 1
            if (lint := lint_proof(body)):
                kid.last_errors = lint
                self.emit("chef", "chef", "lint_reject", f"{kid.lean_name}: {lint}", kid.id)
                continue
            cands.append((kid, body))

        if len(cands) < 2:
            return
        combined = "\n\n".join(self._theorem_text(k, b) for k, b in cands)
        res = await self._check(combined, context=self._context_code())
        if res.ok and res.sorries == 0:
            for kid, body in cands:
                self._mark_verified(kid, body, f"{kid.lean_name} VERIFIED in batched check.")
            return
        self.emit("chef", "chef", "batch_split", f"Batch check failed; splitting {len(cands)} sibling checks.")
        for kid, body in cands:
            res_i = await self._check(self._theorem_text(kid, body), kid, context=self._context_code(kid.id))
            if res_i.ok and res_i.sorries == 0:
                self._mark_verified(kid, body, f"{kid.lean_name} VERIFIED individually.")
            else:
                kid.last_errors = res_i.errors or [f"{res_i.sorries} sorry(ies) remained"]

    async def _sampled_first_attempt(self, node: ProofNode, premises: list[str]) -> bool | None:
        k = max(2, self.cfg.prove_samples)
        helpers = self._verified_context(node.id)
        temps = [0.15 + 0.5 * i / max(1, k - 1) for i in range(k)]
        results = await asyncio.gather(
            *[self._llm(agents.prove(self.llm, node, helpers, [], "", premises, temperature=t)) for t in temps],
            return_exceptions=True,
        )
        bodies: list[str] = []
        for r in results:
            if isinstance(r, BudgetExceeded):
                raise r
            if not isinstance(r, dict) or r.get("claims_false"):
                continue
            body = self._clean_body(r.get("proof", ""))
            if body and not lint_proof(body) and body not in bodies:
                bodies.append(body)
        if not bodies:
            return None
        node.attempts += len(bodies)
        for body in bodies:
            res = await self._check(self._theorem_text(node, body), node, context=self._context_code(node.id))
            if res.ok and res.sorries == 0:
                self._mark_verified(node, body, f"{node.lean_name} VERIFIED (sampled pass@{k}).")
                return True
            node.last_errors = res.errors or [f"{res.sorries} sorry(ies) remained"]
        return False

    async def _prove_node(self, node: ProofNode) -> bool:
        if node.status == NodeStatus.VERIFIED:
            return True
        if self.cfg.verify_policy == "strategic" and await self._probe_lemma_node(node):
            return False
        if await self._try_cascade(node):
            return True
        node.status = NodeStatus.PROVING
        premises = self.index.format_hints(f"{node.informal} {node.lean_statement}", limit=10)
        errors = list(node.last_errors)
        hint = ""
        history: list[str] = []

        if not errors and self.cfg.prove_samples > 1:
            done = await self._sampled_first_attempt(node, premises)
            if done is True:
                return True
            if done is False:
                errors = list(node.last_errors)

        for cycle in range(1, self.cfg.repair_cycles + 1):
            node.attempts += 1
            helpers = self._verified_context(node.id)
            try:
                out = await self._llm(agents.prove(self.llm, node, helpers, errors, hint, premises))
            except LLMError as e:
                errors, hint = [str(e)], ""
                continue
            if out.get("claims_false"):
                node.status = NodeStatus.STUCK
                return False
            body = self._clean_body(out.get("proof", ""))
            self.emit("worker", "prover", "prove_attempt", f"{node.lean_name} attempt {node.attempts}", node.id)
            if (lint := lint_proof(body)):
                errors = lint
                self.emit("chef", "chef", "lint_reject", f"{node.lean_name}: {lint}", node.id)
                history.extend(lint)
                continue
            res = await self._check(self._theorem_text(node, body), node, context=self._context_code(node.id))
            if res.ok and res.sorries == 0:
                self._mark_verified(node, body, f"{node.lean_name} VERIFIED after {node.attempts} attempt(s).")
                return True
            errors = res.errors or [f"{res.sorries} sorry(ies) remained"]
            node.last_errors = errors
            history.extend(errors)
            try:
                crit = await self._llm(agents.critique(self.llm, node, body, errors))
                hint = crit.get("fix_hint", "")
                if crit.get("suggest_decompose") and cycle >= 2:
                    break
            except LLMError:
                hint = ""

        if not node.decomposed and node.depth < self.cfg.max_depth:
            node.decomposed = True
            try:
                dec = await self._llm(agents.decompose(self.llm, node, history))
            except LLMError:
                node.status = NodeStatus.STUCK
                return False
            subs = [
                self._add_node(
                    sp.get("informal", ""),
                    sp.get("sketch", ""),
                    node,
                    name_hint=f"{node.lean_name}_{chr(ord('a') + i)}",
                )
                for i, sp in enumerate(dec.get("lemmas", [])[:3])
            ]
            for s in subs:
                if not await self._formalize_node(s) or not await self._prove_node(s):
                    node.status = NodeStatus.STUCK
                    return False
            node.sketch += f"\nSub-lemmas verified: {[s.lean_name for s in subs]}. {dec.get('recombine_hint', '')}"
            node.last_errors = []
            node.status = NodeStatus.STATEMENT_OK
            return await self._prove_node(node)

        node.status = NodeStatus.STUCK
        return False

    def _assemble_final(self, root: ProofNode) -> str:
        ordered: list[ProofNode] = []
        seen: set[str] = set()

        def visit(n: ProofNode) -> None:
            for c in self.job.children(n.id):
                if c.status == NodeStatus.VERIFIED:
                    visit(c)
            if n.status == NodeStatus.VERIFIED and n.id not in seen:
                seen.add(n.id)
                ordered.append(n)

        visit(root)
        ordered_names = {n.lean_name for n in ordered if n.lean_name}
        ledger_by_name = {
            n.lean_name: n
            for n in self.ledger.get_verified()
            if n.lean_name and n.lean_name not in ordered_names
        }
        needed_names: set[str] = set()
        frontier = [self._theorem_text(n, n.lean_proof) for n in ordered]
        while frontier:
            joined = "\n".join(frontier)
            frontier = []
            for name, lnode in ledger_by_name.items():
                if name in needed_names:
                    continue
                if re.search(rf"\b{re.escape(name)}\b", joined):
                    needed_names.add(name)
                    frontier.append(self._theorem_text(lnode, lnode.lean_proof))
        needed = [n for n in ledger_by_name.values() if n.lean_name in needed_names]
        full_order = needed + ordered
        return "\n\n".join(self._theorem_text(n, n.lean_proof) for n in full_order)

    def _failures(self, prefix: str) -> str:
        stuck = [f"{n.lean_name}: {n.last_errors[:1]}" for n in self.job.nodes.values() if n.status == NodeStatus.STUCK]
        return f"{prefix}: {stuck[:5]}"
