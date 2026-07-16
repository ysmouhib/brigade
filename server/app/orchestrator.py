"""The Chef's control loop.

Hierarchy (kitchen-brigade shaped):

    Chef (this file)  — owns the proof ledger (a DAG of lemmas), budgets, and acceptance.
      ├─ Skeptic            — numeric falsification BEFORE any proving effort (sympy).
      ├─ Brainstormers ×k   — parallel high-temperature intuition agents (personas).
      ├─ Sous-Chef          — merges strategies into a lemma decomposition.
      ├─ Formalizer cooks   — per-lemma autoformalization, gated by Lean (`:= by sorry`).
      ├─ Prover cooks       — per-lemma proof search: attempt → Lean errors → Critic → repair.
      ├─ Critic (Expeditor) — triages Lean errors into targeted fix hints.
      └─ Lean verifier      — NOT an LLM. The only entity allowed to mark anything true.

Invariants enforced here (and tested in tests/):
  I1  A node becomes VERIFIED only immediately after a LeanVerifier.check() with
      ok=True and sorries=0 on code containing that node.
  I2  A job becomes PROVED only after the fully assembled file passes a fresh Lean
      check AND an axiom audit (no sorryAx / custom axioms).
  I3  Statements are pinned after the statement gate; provers can only supply tactic
      bodies, so they can never weaken what is being proved.
  I4  Proof bodies are linted against forbidden tokens (sorry/axiom/native_decide/...)
      before Lean is even consulted.
"""
from __future__ import annotations
import asyncio
import re
import textwrap
import traceback

from . import agents, numeric, retrieval
from .config import Config
from .llm import LLM, LLMError
from .models import AgentEvent, Job, JobStatus, NodeStatus, ProofNode, Refutation, new_id
from .lean.verifier import LeanVerifier, lint_proof

NAME_RE = re.compile(r"[^A-Za-z0-9_']")

# Zero-LLM first pass: one Lean call trying the powerful closers. If any branch closes
# the pinned goal the lemma is VERIFIED for the cost of a single check and no tokens.
CASCADE_BODY = ("first\n"
                "  | omega\n  | ring\n  | norm_num\n  | positivity\n"
                "  | nlinarith\n  | simp\n  | aesop\n  | decide")


class BudgetExceeded(Exception):
    pass


class Orchestrator:
    def __init__(self, job: Job, llm: LLM, lean: LeanVerifier, cfg: Config):
        self.job, self.llm, self.lean, self.cfg = job, llm, lean, cfg
        self._seq = 0
        self._names: set[str] = set()

    # ---------------------------------------------------------------- events
    def emit(self, level: str, agent: str, type_: str, content: str, node_id: str | None = None):
        self._seq += 1
        self.job.events.append(AgentEvent(seq=self._seq, level=level, agent=agent,
                                          type=type_, content=content[:4000], node_id=node_id))
        if len(self.job.events) > 4000:
            del self.job.events[: len(self.job.events) - 4000]

    # ---------------------------------------------------------------- budget-aware wrappers
    async def _llm(self, coro):
        if self.job.llm_calls >= self.cfg.max_llm_calls:
            raise BudgetExceeded("LLM call budget exhausted")
        self.job.llm_calls += 1
        return await coro

    async def _check(self, code: str, node: ProofNode | None = None, context: str = ""):
        if self.job.lean_calls >= self.cfg.max_lean_calls:
            raise BudgetExceeded("Lean call budget exhausted")
        self.job.lean_calls += 1
        res = await self.lean.check(code, context=context)
        self.emit("lean", "lean_verifier", "lean_check", res.summary(),
                  node.id if node else None)
        return res

    # ---------------------------------------------------------------- naming / code assembly
    def _unique_name(self, raw: str) -> str:
        base = NAME_RE.sub("_", raw.strip()) or "lemma"
        if base[0].isdigit():
            base = "l_" + base
        name, i = base, 1
        while name in self._names:
            i += 1
            name = f"{base}_{i}"
        self._names.add(name)
        return name

    @staticmethod
    def _theorem_text(node: ProofNode, body: str) -> str:
        indented = textwrap.indent(body.strip(), "  ")
        return f"{node.lean_statement.strip()} := by\n{indented}"

    def _verified_context(self, exclude: str | None = None) -> list[ProofNode]:
        """All VERIFIED nodes in creation (≈ topological) order."""
        return [n for n in self.job.nodes.values()
                if n.status == NodeStatus.VERIFIED and n.id != exclude]

    def _code_with_context(self, node: ProofNode, body: str) -> str:
        parts = [self._theorem_text(h, h.lean_proof) for h in self._verified_context(node.id)]
        parts.append(self._theorem_text(node, body))
        return "\n\n".join(parts)

    def _context_code(self, exclude: str | None = None) -> str:
        """Verified helpers as one code block, passed separately so the REPL backend can
        elaborate it once and reuse the environment across checks."""
        return "\n\n".join(self._theorem_text(h, h.lean_proof)
                            for h in self._verified_context(exclude))

    async def _retrieve(self, node: ProofNode) -> list[str]:
        """Best-effort Mathlib premise retrieval; advisory prompt text only."""
        if self.cfg.retrieval == "off":
            return []
        query = node.informal or node.lean_statement
        hits = await retrieval.search(self.cfg.retrieval, query)
        if hits:
            self.emit("worker", "retriever", "premises",
                      f"{node.lean_name}: {len(hits)} candidate declaration(s) from "
                      f"{self.cfg.retrieval}:\n" + "\n".join(hits[:6]), node.id)
        return hits

    async def _try_cascade(self, node: ProofNode) -> bool:
        """One symbolic-automation Lean call before spending any prover tokens."""
        if not self.cfg.tactic_cascade or node.status != NodeStatus.STATEMENT_OK:
            return False
        res = await self._check(self._theorem_text(node, CASCADE_BODY), node,
                                context=self._context_code(node.id))
        if res.ok and res.sorries == 0:
            node.lean_proof, node.status, node.last_errors = CASCADE_BODY, NodeStatus.VERIFIED, []
            self.emit("chef", "chef", "verified",
                      f"{node.lean_name} VERIFIED by the tactic cascade (0 LLM calls).", node.id)
            return True
        return False

    def _clean_body(self, node: ProofNode, raw: str) -> str:
        """Strip a repeated header if the prover echoed the theorem line (I3)."""
        body = raw.strip()
        body = re.sub(r"^```(?:lean4?|lean)?\s*|\s*```$", "", body).strip()
        if body.startswith(("theorem", "lemma")):
            m = re.search(r":=\s*by\b", body)
            body = body[m.end():].strip() if m else body
        if body.startswith("by\n") or body == "by":
            body = body[2:].strip()
        elif body.startswith("by "):
            body = body[3:].strip()
        return textwrap.dedent(body)

    # ---------------------------------------------------------------- node creation
    def _add_node(self, informal: str, sketch: str, parent: ProofNode | None,
                  kind: str = "lemma", name_hint: str = "") -> ProofNode:
        node = ProofNode(kind=kind, informal=informal, sketch=sketch,
                         parent_id=parent.id if parent else None,
                         depth=(parent.depth + 1) if parent else 0)
        node.lean_name = self._unique_name(name_hint or ("thm_main" if kind == "theorem"
                                                         else f"lemma_{len(self.job.nodes)}"))
        self.job.nodes[node.id] = node
        return node

    # ================================================================ top level
    async def run(self):
        job = self.job
        job.status = JobStatus.RUNNING
        try:
            await self._run()
        except asyncio.CancelledError:
            job.status = JobStatus.CANCELLED
            job.phase = "cancelled"
            self.emit("system", "system", "cancelled", "job cancelled by user")
        except BudgetExceeded as e:
            job.status = JobStatus.EXHAUSTED
            job.phase = "exhausted"
            self.emit("chef", "chef", "budget", str(e))
            await self._write_report()
        except Exception:  # noqa: BLE001 — surface, never hang
            job.status = JobStatus.ERROR
            job.phase = "error"
            self.emit("system", "system", "error", traceback.format_exc()[-1500:])
        # NOTE: the verifier is shared across jobs (warm REPL); the app closes it on shutdown.

    async def _run(self):
        job, cfg = self.job, self.cfg
        self.emit("chef", "chef", "start", f"Problem received: {job.problem[:300]}")

        # -------- Phase 0: the Skeptic tries to kill the claim numerically --------
        job.phase = "skeptic"
        try:
            hunt = await self._llm(agents.skeptic(self.llm, job.problem))
            if hunt.get("is_checkable") and hunt.get("claim_expr"):
                self.emit("worker", "skeptic", "probe",
                          f"probing '{hunt['claim_expr']}' at {len(hunt.get('candidates', []))} candidates")
                cex = numeric.find_counterexample(hunt["claim_expr"], hunt.get("candidates", []))
                if cex is not None:
                    job.refutation = Refutation(counterexample=cex, claim_expr=hunt["claim_expr"],
                                                note=hunt.get("notes", ""))
                    job.status = JobStatus.REFUTED
                    job.phase = "refuted"
                    self.emit("chef", "chef", "refuted",
                              f"Numeric counterexample found: {cex}. No proof attempted.")
                    await self._write_report()
                    return
                self.emit("worker", "skeptic", "probe_result", "no counterexample found; proceeding")
        except (LLMError, numeric.ProbeError) as e:
            self.emit("worker", "skeptic", "probe_skipped", f"skeptic inconclusive: {e}")

        # -------- Rounds: brainstorm → plan → formalize → prove → assemble --------
        feedback = ""
        for rnd in range(1, cfg.max_rounds + 1):
            job.round = rnd
            self.emit("chef", "chef", "round", f"=== Round {rnd}/{cfg.max_rounds} ===")

            # 1. parallel brainstorm crew
            job.phase = "brainstorm"
            from .prompts import PERSONAS
            personas = PERSONAS[: max(1, cfg.n_brainstormers)]
            results = await asyncio.gather(
                *[self._llm(agents.brainstorm(self.llm, job.problem, p, feedback)) for p in personas],
                return_exceptions=True)
            strategies = []
            for p, r in zip(personas, results):
                if isinstance(r, Exception):
                    self.emit("worker", "brainstormer", "failed", f"{p}: {r}")
                else:
                    strategies.append(r)
                    self.emit("worker", f"brainstormer:{p.split()[1]}", "strategy",
                              f"{r.get('strategy_name', '?')}: {r.get('proof_sketch', '')[:400]}")
            if not strategies:
                feedback = "all brainstormers failed to produce strategies"
                continue

            # 2. sous-chef merges into a plan
            job.phase = "plan"
            plan = await self._llm(agents.strategize(self.llm, job.problem, strategies, feedback))
            self.emit("sous", "strategist", "plan",
                      f"strategy '{plan.get('chosen_strategy', '?')}' with "
                      f"{len(plan.get('lemmas', []))} lemma(s). {plan.get('assembly_note', '')[:300]}")

            root = self._add_node(plan.get("main_theorem_informal", job.problem),
                                  plan.get("assembly_note", ""), None, kind="theorem")
            job.root_id = root.id
            lemmas = [self._add_node(sp.get("informal", ""), sp.get("sketch", ""), root)
                      for sp in plan.get("lemmas", [])[:5]]

            # 3. formalization gate (statements must compile with `by sorry`)
            job.phase = "formalize"
            gate_ok = True
            for node in lemmas + [root]:
                if not await self._formalize_node(node):
                    gate_ok = False
            if not gate_ok or root.status != NodeStatus.STATEMENT_OK:
                feedback = self._failures("formalization gate failed")
                self._abandon_round()
                continue

            # 4. prove the tree bottom-up with repair cycles + decomposition escalation
            job.phase = "prove"
            proved = await self._prove_subtree(root)

            # 5. assemble + final verification + axiom audit
            if proved:
                job.phase = "assemble"
                final_code = "\n\n".join(self._theorem_text(n, n.lean_proof)
                                         for n in self._topo_order())
                res = await self._check(final_code)
                lint = lint_proof(final_code)
                if res.ok and res.sorries == 0 and not lint:
                    audit = await self.lean.axiom_audit(final_code, root.lean_name)
                    self.emit("lean", "lean_verifier", "axiom_audit",
                              f"ok={audit.ok} axioms={audit.axioms} {audit.note}")
                    if audit.ok:
                        job.final_lean = final_code
                        job.status = JobStatus.PROVED
                        job.phase = "proved"
                        self.emit("chef", "chef", "proved",
                                  f"Final theorem '{root.lean_name}' verified by Lean "
                                  f"(round {rnd}, {job.lean_calls} Lean checks, {job.llm_calls} LLM calls).")
                        await self._write_report()
                        return
                    feedback = f"axiom audit failed: {audit.note}"
                else:
                    feedback = f"final assembly failed: {lint or res.errors[:3]}"
                self.emit("chef", "chef", "assembly_failed", feedback)
            else:
                feedback = self._failures("proving failed")

            # 6. retrospective feeds the next round
            try:
                retro = await self._llm(agents.retrospective(self.llm, job.problem, feedback))
                feedback = f"{retro.get('summary', '')} INSTRUCTIONS: {retro.get('instructions', '')}"
                self.emit("chef", "chef", "retrospective", feedback[:800])
            except LLMError:
                pass
            self._abandon_round()

        job.status = JobStatus.EXHAUSTED
        job.phase = "exhausted"
        self.emit("chef", "chef", "exhausted",
                  f"All {cfg.max_rounds} rounds spent. Verified lemmas are reported as partial progress.")
        await self._write_report()

    # ---------------------------------------------------------------- phases
    async def _formalize_node(self, node: ProofNode) -> bool:
        errors: list[str] = []
        for attempt in range(self.cfg.statement_retries):
            try:
                out = await self._llm(agents.formalize(self.llm, node, self.job.problem, errors,
                                                       retrieved=await self._retrieve(node)))
            except LLMError as e:
                errors = [str(e)]
                continue
            stmt = out.get("lean_statement", "").strip()
            # pin the given name (I3): normalize `theorem <anything>` → `theorem <lean_name>`
            stmt = re.sub(r"^(theorem|lemma)\s+[A-Za-z0-9_']+", f"theorem {node.lean_name}", stmt)
            if not stmt.startswith("theorem"):
                stmt = f"theorem {node.lean_name} : {stmt}"
            node.lean_statement = stmt.split(":=")[0].strip()
            self.emit("worker", "formalizer", "statement_attempt", node.lean_statement, node.id)
            res = await self._check(self._theorem_text(node, "sorry"), node,
                                    context=self._context_code(node.id))
            if res.ok:  # errors empty; sorries expected
                if res.goals:
                    node.goal = res.goals[0]
                node.status = NodeStatus.STATEMENT_OK
                self.emit("worker", "formalizer", "statement_ok",
                          f"{node.lean_name}: statement elaborates", node.id)
                return True
            errors = res.errors
            node.last_errors = errors
        node.status = NodeStatus.STUCK
        self.emit("chef", "chef", "statement_stuck",
                  f"{node.lean_name}: statement never elaborated: {errors[:2]}", node.id)
        return False

    async def _prove_subtree(self, node: ProofNode) -> bool:
        kids = [c for c in self.job.children(node.id) if c.status != NodeStatus.VERIFIED]
        if self.cfg.verify_policy == "strategic" and len(kids) >= 2:
            if not await self._strategic_batch(kids):
                node.status = NodeStatus.STUCK
                return False
        for child in self.job.children(node.id):
            if child.status == NodeStatus.VERIFIED:
                continue
            if not await self._prove_subtree(child):
                node.status = NodeStatus.STUCK
                return False
        return await self._prove_node(node)

    async def _probe_lemma(self, node: ProofNode) -> bool:
        """Strategic pre-check: try to numerically REFUTE a planned lemma before proving.
        Returns True if the lemma was refuted (caller must abort the plan)."""
        if node.probed or node.kind != "lemma":
            return False
        node.probed = True
        try:
            hunt = await self._llm(agents.skeptic(self.llm, node.informal))
            if not (hunt.get("is_checkable") and hunt.get("claim_expr")):
                return False
            self.emit("worker", "skeptic", "probe",
                      f"{node.lean_name}: probing '{hunt['claim_expr']}' "
                      f"at {len(hunt.get('candidates', []))} candidates", node.id)
            cex = numeric.find_counterexample(hunt["claim_expr"], hunt.get("candidates", []))
            if cex is not None:
                node.status = NodeStatus.REFUTED
                node.last_errors = [f"numerically refuted at {cex}"]
                self.emit("chef", "chef", "lemma_refuted",
                          f"{node.lean_name} is FALSE at {cex} — plan abandoned before proving.",
                          node.id)
                return True
            self.emit("worker", "skeptic", "probe_result",
                      f"{node.lean_name}: no counterexample on the grid", node.id)
        except (LLMError, numeric.ProbeError, BudgetExceeded) as e:
            if isinstance(e, BudgetExceeded):
                raise
            self.emit("worker", "skeptic", "probe_skipped",
                      f"{node.lean_name}: probe inconclusive: {e}", node.id)
        return False

    async def _strategic_batch(self, kids: list[ProofNode]) -> bool:
        """Strategic mode: probe each sibling lemma, then verify all first attempts in ONE
        Lean call (imports elaborate once instead of N times). On a batch failure, fall back
        to individual checks so the Critic gets per-node errors. Acceptance semantics are
        unchanged: a node is VERIFIED only because Lean compiled its theorem with no errors
        and no sorries — batching only changes how many theorems share a compilation unit."""
        for kid in kids:
            if await self._probe_lemma(kid):
                return False
        cands: list[tuple[ProofNode, str]] = []
        for kid in kids:
            if kid.status != NodeStatus.STATEMENT_OK:
                continue
            if await self._try_cascade(kid):
                continue
            helpers = self._verified_context(kid.id)
            try:
                out = await self._llm(agents.prove(self.llm, kid, helpers, [], "",
                                                   retrieved=await self._retrieve(kid)))
            except LLMError as e:
                kid.last_errors = [str(e)]
                continue
            if out.get("claims_false"):
                self.emit("worker", "prover", "claims_false",
                          f"{kid.lean_name}: prover believes the statement is false: "
                          f"{out.get('why', '')[:300]}", kid.id)
                continue
            body = self._clean_body(kid, out.get("proof", ""))
            kid.attempts += 1
            self.emit("worker", "prover", "prove_attempt",
                      f"{kid.lean_name} attempt {kid.attempts} (batched):\n{body[:600]}", kid.id)
            if (lint := lint_proof(body)):
                kid.last_errors = lint
                self.emit("chef", "chef", "lint_reject", f"{kid.lean_name}: {lint}", kid.id)
                continue
            cands.append((kid, body))
        if len(cands) < 2:
            return True
        combined = "\n\n".join(self._theorem_text(k, b) for k, b in cands)
        res = await self._check(combined, context=self._context_code())
        if res.ok and res.sorries == 0:
            for kid, body in cands:
                kid.lean_proof, kid.status, kid.last_errors = body, NodeStatus.VERIFIED, []
                self.emit("chef", "chef", "verified",
                          f"{kid.lean_name} VERIFIED by Lean (batched check, 1 attempt).", kid.id)
            return True
        self.emit("chef", "chef", "batch_split",
                  f"batched check failed ({res.errors[:2]}); re-checking "
                  f"{len(cands)} candidates individually")
        for kid, body in cands:
            res_i = await self._check(self._theorem_text(kid, body), kid,
                                      context=self._context_code(kid.id))
            if res_i.ok and res_i.sorries == 0:
                kid.lean_proof, kid.status, kid.last_errors = body, NodeStatus.VERIFIED, []
                self.emit("chef", "chef", "verified",
                          f"{kid.lean_name} VERIFIED by Lean after {kid.attempts} attempt(s).",
                          kid.id)
            else:
                kid.last_errors = res_i.errors or [f"{res_i.sorries} sorry(ies) remained"]
        return True

    async def _sampled_first_attempt(self, node: ProofNode,
                                     retrieved: list[str]) -> bool | None:
        """Fire k parallel prover candidates at spread temperatures, then verify until
        one passes (pass@k instead of pass@1 on the first attempt). Returns True on
        verification, False if all candidates failed (last errors kept for repair),
        None if nothing usable came back (fall through to the normal loop untouched)."""
        k = max(2, self.cfg.prove_samples)
        helpers = self._verified_context(node.id)
        temps = [0.2 + 0.6 * i / max(1, k - 1) for i in range(k)]
        results = await asyncio.gather(
            *[self._llm(agents.prove(self.llm, node, helpers, [], "",
                                     retrieved=retrieved, temperature=t)) for t in temps],
            return_exceptions=True)
        bodies: list[str] = []
        for r in results:
            if isinstance(r, BudgetExceeded):
                raise r
            if isinstance(r, Exception) or r.get("claims_false"):
                continue
            body = self._clean_body(node, r.get("proof", ""))
            if body and not lint_proof(body) and body not in bodies:
                bodies.append(body)
        if not bodies:
            return None
        node.attempts += len(bodies)
        self.emit("worker", "prover", "prove_attempt",
                  f"{node.lean_name}: {len(bodies)} sampled candidate(s) at temperatures "
                  f"{[round(t, 2) for t in temps[:len(bodies)]]}", node.id)
        for body in bodies:
            res = await self._check(self._theorem_text(node, body), node,
                                    context=self._context_code(node.id))
            if res.ok and res.sorries == 0:
                node.lean_proof, node.status, node.last_errors = body, NodeStatus.VERIFIED, []
                self.emit("chef", "chef", "verified",
                          f"{node.lean_name} VERIFIED by Lean (sampled candidates).", node.id)
                return True
            node.last_errors = res.errors or [f"{res.sorries} sorry(ies) remained"]
        return False

    async def _prove_node(self, node: ProofNode) -> bool:
        if node.status == NodeStatus.VERIFIED:
            return True
        if self.cfg.verify_policy == "strategic" and await self._probe_lemma(node):
            return False
        if await self._try_cascade(node):
            return True
        node.status = NodeStatus.PROVING
        retrieved = await self._retrieve(node)
        errors: list[str] = list(node.last_errors)
        hint = ""
        history: list[str] = []
        if not errors and self.cfg.prove_samples > 1:
            done = await self._sampled_first_attempt(node, retrieved)
            if done is not None:
                if done:
                    return True
                errors = list(node.last_errors)
        for cycle in range(1, self.cfg.repair_cycles + 1):
            node.attempts += 1
            helpers = [c for c in self.job.children(node.id) if c.status == NodeStatus.VERIFIED]
            helpers += [n for n in self._verified_context(node.id) if n not in helpers]
            try:
                out = await self._llm(agents.prove(self.llm, node, helpers, errors, hint,
                                                   retrieved=retrieved))
            except LLMError as e:
                errors, hint = [str(e)], ""
                continue
            if out.get("claims_false"):
                self.emit("worker", "prover", "claims_false",
                          f"{node.lean_name}: prover believes the statement is false: "
                          f"{out.get('why', '')[:300]}", node.id)
                node.status = NodeStatus.STUCK
                history.append("prover claims statement false")
                break
            body = self._clean_body(node, out.get("proof", ""))
            self.emit("worker", "prover", "prove_attempt",
                      f"{node.lean_name} attempt {node.attempts}:\n{body[:600]}", node.id)
            lint = lint_proof(body)
            if lint:  # I4 — reject before Lean is consulted
                errors = lint
                self.emit("chef", "chef", "lint_reject", f"{node.lean_name}: {lint}", node.id)
                history.extend(lint)
                continue
            res = await self._check(self._theorem_text(node, body), node,
                                    context=self._context_code(node.id))
            if res.ok and res.sorries == 0:
                node.lean_proof = body
                node.status = NodeStatus.VERIFIED  # I1 — only here and only after ok
                node.last_errors = []
                self.emit("chef", "chef", "verified",
                          f"{node.lean_name} VERIFIED by Lean after {node.attempts} attempt(s).", node.id)
                return True
            errors = res.errors or [f"{res.sorries} sorry(ies) remained"]
            node.last_errors = errors
            history.extend(errors)
            try:
                crit = await self._llm(agents.critique(self.llm, node, body, errors))
                hint = crit.get("fix_hint", "")
                self.emit("sous", "critic", "triage",
                          f"{node.lean_name}: {crit.get('diagnosis', '')[:200]} → {hint[:200]}", node.id)
                if crit.get("suggest_decompose") and cycle >= 2:
                    break
            except LLMError:
                hint = ""

        # escalation: split into sub-lemmas once, if depth allows
        if not node.decomposed and node.depth < self.cfg.max_depth:
            node.decomposed = True
            try:
                dec = await self._llm(agents.decompose(self.llm, node, history))
            except LLMError as e:
                self.emit("chef", "chef", "decompose_failed", str(e), node.id)
                node.status = NodeStatus.STUCK
                return False
            subs = [self._add_node(sp.get("informal", ""), sp.get("sketch", ""), node,
                                   name_hint=f"{node.lean_name}_{chr(ord('a') + i)}")
                    for i, sp in enumerate(dec.get("lemmas", [])[:3])]
            self.emit("chef", "chef", "decompose",
                      f"{node.lean_name} split into {[s.lean_name for s in subs]}. "
                      f"{dec.get('recombine_hint', '')[:200]}", node.id)
            for s in subs:
                if not await self._formalize_node(s) or not await self._prove_node(s):
                    node.status = NodeStatus.STUCK
                    return False
            node.sketch += f"\nUse the verified sub-lemmas: {', '.join(s.lean_name for s in subs)}. " \
                           f"{dec.get('recombine_hint', '')}"
            node.last_errors = []
            node.status = NodeStatus.PROVING
            # one fresh batch of repair cycles now that sub-lemmas exist
            saved, self.cfg.repair_cycles = self.cfg.repair_cycles, max(2, self.cfg.repair_cycles)
            try:
                return await self._retry_after_decompose(node)
            finally:
                self.cfg.repair_cycles = saved
        node.status = NodeStatus.STUCK
        return False

    async def _retry_after_decompose(self, node: ProofNode) -> bool:
        node.decomposed = True  # guard against infinite recursion
        errors: list[str] = []
        hint = "Cite the newly verified sub-lemmas by name."
        for _ in range(self.cfg.repair_cycles):
            node.attempts += 1
            helpers = [c for c in self.job.children(node.id) if c.status == NodeStatus.VERIFIED]
            try:
                out = await self._llm(agents.prove(self.llm, node, helpers, errors, hint))
            except LLMError as e:
                errors = [str(e)]
                continue
            body = self._clean_body(node, out.get("proof", ""))
            self.emit("worker", "prover", "prove_attempt",
                      f"{node.lean_name} (post-split) attempt {node.attempts}:\n{body[:600]}", node.id)
            if (lint := lint_proof(body)):
                errors = lint
                continue
            res = await self._check(self._theorem_text(node, body), node,
                                    context=self._context_code(node.id))
            if res.ok and res.sorries == 0:
                node.lean_proof, node.status, node.last_errors = body, NodeStatus.VERIFIED, []
                self.emit("chef", "chef", "verified",
                          f"{node.lean_name} VERIFIED after decomposition.", node.id)
                return True
            errors = res.errors or ["sorries remained"]
        node.status = NodeStatus.STUCK
        return False

    # ---------------------------------------------------------------- helpers
    def _topo_order(self) -> list[ProofNode]:
        """Children before parents; root last. All must be VERIFIED when called."""
        out: list[ProofNode] = []

        def visit(n: ProofNode):
            for c in self.job.children(n.id):
                if c.status == NodeStatus.VERIFIED:
                    visit(c)
            out.append(n)

        visit(self.job.root())
        return out

    def _failures(self, prefix: str) -> str:
        stuck = [f"{n.lean_name}: {n.last_errors[:1]}" for n in self.job.nodes.values()
                 if n.status in (NodeStatus.STUCK, NodeStatus.REFUTED)]
        return f"{prefix}. Stuck/refuted nodes: {stuck[:6]}"

    def _abandon_round(self):
        for n in self.job.nodes.values():
            if n.status not in (NodeStatus.VERIFIED, NodeStatus.REFUTED):
                n.status = NodeStatus.ABANDONED

    async def _write_report(self):
        job = self.job
        verified = [n.lean_name for n in job.nodes.values() if n.status == NodeStatus.VERIFIED]
        outcome = (f"status={job.status.value}; verified_lemmas={verified}; "
                   f"refutation={job.refutation.model_dump() if job.refutation else None}; "
                   f"lean_calls={job.lean_calls}")
        try:
            rep = await self._llm(agents.final_report(self.llm, job.problem, outcome))
            job.summary = rep.get("report", outcome)
        except (LLMError, BudgetExceeded):
            job.summary = outcome
