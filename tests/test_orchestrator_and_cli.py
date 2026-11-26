"""End-to-end tests for PremiseIndex, ProofLedger, Orchestrator (I1-I4), and CLI."""

from __future__ import annotations

from pathlib import Path
import tempfile
import unittest

from brigade.bench import run_benchmark_suite
from brigade.cli import main as cli_main
from brigade.lean_verifier import RealLeanVerifier
from brigade.library_index import PremiseIndex, ProofLedger
from brigade.llm import ScriptedLLM
from brigade.models import Job, JobStatus, NodeStatus, ProofNode
from brigade.orchestrator import Orchestrator, OrchestratorConfig

PROJECT_DIR = Path(__file__).resolve().parent.parent


class TestOrchestratorAndCLI(unittest.IsolatedAsyncioTestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.verifier = RealLeanVerifier(PROJECT_DIR, timeout_s=60.0)

    def test_premise_index_discovers_hj_theorems(self) -> None:
        idx = PremiseIndex(PROJECT_DIR)
        names = {e.name for e in idx.entries}
        for expected in (
            "HJUpper",
            "fin_pigeonhole",
            "finEquivFun",
            "hj_two_exact",
            "color_focused_dichotomy",
            "shelah_equal_ends",
            "hales_jewett_shelah",
            "hales_jewett",
            "van_der_waerden",
            "hj_implies_vdw",
            "checkCertSym2_sound",
            "checkCertSym_sound",
        ):
            self.assertIn(expected, names)
        hits = idx.search("ColorFocused dichotomy", limit=5)
        self.assertTrue(any(h.name == "color_focused_dichotomy" for h in hits))

    def test_proof_ledger_enforces_i1_and_persists(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            ledger_path = Path(tmp) / "ledger.json"
            ledger = ProofLedger(ledger_path)

            unverified = ProofNode(lean_name="bad_node", status=NodeStatus.PROVING)
            with self.assertRaises(ValueError):
                ledger.add_verified(unverified)

            good = ProofNode(
                lean_name="ok_hj_2_3",
                lean_statement="theorem ok_hj_2_3 : HJUpper 3 2 3",
                lean_proof="exact hj_two_upper 3",
                status=NodeStatus.VERIFIED,
            )
            ledger.add_verified(good)

            reloaded = ProofLedger(ledger_path)
            found = reloaded.find_matching_statement("theorem ok_hj_2_3 : HJUpper 3 2 3")
            self.assertIsNotNone(found)
            assert found is not None
            self.assertEqual(found.lean_proof, "exact hj_two_upper 3")

    async def test_phase0_skeptic_refutes_and_proves_with_real_lean(self) -> None:
        def fail_if_called(role: str, _sys: str, _usr: str):
            raise AssertionError(f"LLM should not be called for finite HJ Skeptic check: {role}")

        with tempfile.TemporaryDirectory() as tmp:
            cfg = OrchestratorConfig(project_dir=PROJECT_DIR, ledger_path=Path(tmp) / "l.json")
            # Refutation of false upper bound HJUpper 3 3 2
            job_ref = Job(problem="Prove HJUpper 3 3 2")
            await Orchestrator(job_ref, ScriptedLLM(fail_if_called), self.verifier, cfg).run()
            self.assertEqual(job_ref.status, JobStatus.REFUTED)
            self.assertIsNotNone(job_ref.refutation)
            assert job_ref.refutation is not None
            self.assertTrue(job_ref.refutation.lean_verified)

            # Proof of HJUpper 4 3 2 via CertTree
            job_ok = Job(problem="Prove HJUpper 4 3 2")
            await Orchestrator(job_ok, ScriptedLLM(fail_if_called), self.verifier, cfg).run()
            self.assertEqual(job_ok.status, JobStatus.PROVED)
            self.assertIn("checkCertSym2_sound", job_ok.final_lean)

    async def test_orchestrator_batch_split_repair_i3_and_i4_with_real_lean(self) -> None:
        prover_attempts: dict[str, int] = {}

        def handler(role: str, _sys: str, user: str) -> dict:
            if role == "skeptic":
                return {"is_hj_finite_query": False}
            if role == "brainstormer":
                return {
                    "strategy_name": "HJ monotonicity",
                    "key_ideas": ["Use hj_two_upper and HJUpper.mono_dim"],
                    "proof_sketch": "Prove dimension-3 then lift to dimension-4.",
                    "candidate_lemmas": ["HJUpper 3 2 3", "HJUpper 4 2 4"],
                    "confidence": 0.95,
                }
            if role == "strategist":
                return {
                    "chosen_strategy": "HJ monotonicity",
                    "main_theorem_informal": "HJUpper 4 2 3 holds",
                    "lemmas": [
                        {"informal": "HJUpper 3 2 3", "sketch": "hj_two_upper", "difficulty": 1},
                        {"informal": "HJUpper 4 2 4", "sketch": "hj_two_upper", "difficulty": 1},
                    ],
                    "assembly_note": "Lift HJUpper 3 2 3 to dim 4 using mono_dim.",
                }
            if role == "formalizer":
                if "TARGET lean_name: thm_main" in user:
                    return {
                        "lean_statement": "theorem thm_main : HJUpper 4 2 3",
                        "faithfulness_note": "exact",
                    }
                if "TARGET lean_name: lemma_1" in user:
                    return {
                        "lean_statement": "theorem lemma_1 : HJUpper 3 2 3",
                        "faithfulness_note": "exact",
                    }
                return {
                    "lean_statement": "theorem lemma_2 : HJUpper 4 2 4",
                    "faithfulness_note": "exact",
                }
            if role == "prover":
                if "TARGET lean_name: lemma_1" in user:
                    # Succeeds in batched sibling check (I3: echoed fake header must be stripped)
                    return {
                        "proof": "theorem sneaky_weak : True := by\n  exact hj_two_upper 3",
                        "claims_false": False,
                        "why": "",
                    }
                if "TARGET lean_name: lemma_2" in user:
                    cnt = prover_attempts.get("lemma_2", 0) + 1
                    prover_attempts["lemma_2"] = cnt
                    if cnt == 1:
                        # Fails batch check -> forces batch_split + repair cycle
                        return {"proof": "exact hj_two_upper 3", "claims_false": False, "why": ""}
                    return {"proof": "exact hj_two_upper 4", "claims_false": False, "why": ""}
                # Root theorem thm_main: attempt 1 tries `sorry` (caught by I4 lint!), attempt 2 succeeds
                cnt = prover_attempts.get("thm_main", 0) + 1
                prover_attempts["thm_main"] = cnt
                if cnt == 1:
                    return {"proof": "sorry", "claims_false": False, "why": ""}
                return {
                    "proof": "exact HJUpper.mono_dim (by decide) (by decide) lemma_1",
                    "claims_false": False,
                    "why": "",
                }
            if role == "critic":
                return {
                    "diagnosis": "Type mismatch on color bound",
                    "fix_hint": "Pass 4 instead of 3 to hj_two_upper.",
                    "suggest_decompose": False,
                }
            raise AssertionError(f"Unexpected role {role}")

        with tempfile.TemporaryDirectory() as tmp:
            ledger_file = Path(tmp) / "ledger.json"
            cfg = OrchestratorConfig(
                project_dir=PROJECT_DIR,
                enable_skeptic=False,
                tactic_cascade=False,  # Exercise batched verification, batch_split, I3, I4, and Critic
                prove_samples=1,
                n_brainstormers=1,
                ledger_path=ledger_file,
            )
            job = Job(problem="Prove that HJUpper 4 2 3 holds via dimension monotonicity.")
            await Orchestrator(job, ScriptedLLM(handler), self.verifier, cfg).run()

            self.assertEqual(job.status, JobStatus.PROVED, job.summary)
            ev_types = [e.type for e in job.events]
            self.assertIn("batch_split", ev_types)
            self.assertIn("lint_reject", ev_types)
            self.assertIn("axiom_audit", ev_types)
            self.assertNotIn("sneaky_weak", job.final_lean)
            self.assertIn("theorem thm_main : HJUpper 4 2 3", job.final_lean)

            # Persistent ledger preserved all verified nodes
            reloaded = ProofLedger(ledger_file)
            self.assertGreaterEqual(len(reloaded.get_verified()), 3)

    async def test_per_lemma_skeptic_kills_false_sublemma_before_prover(self) -> None:
        def handler(role: str, _sys: str, user: str) -> dict:
            if role == "brainstormer":
                return {
                    "strategy_name": "Overly optimistic bound",
                    "key_ideas": ["Assume HJUpper 3 3 2"],
                    "proof_sketch": "Use HJUpper 3 3 2 to prove something.",
                    "candidate_lemmas": ["HJUpper 3 3 2"],
                    "confidence": 0.9,
                }
            if role == "strategist":
                return {
                    "chosen_strategy": "Optimistic",
                    "main_theorem_informal": "HJUpper 4 3 2",
                    "lemmas": [
                        {"informal": "HJUpper 3 3 2", "sketch": "false lemma", "difficulty": 2}
                    ],
                    "assembly_note": "Lift from dim 3 to dim 4.",
                }
            if role == "formalizer":
                if "TARGET lean_name: thm_main" in user:
                    return {"lean_statement": "theorem thm_main : HJUpper 4 3 2", "faithfulness_note": "ok"}
                return {"lean_statement": "theorem lemma_1 : HJUpper 3 3 2", "faithfulness_note": "ok"}
            if role == "prover":
                raise AssertionError("Prover should NEVER be consulted on a false lemma caught by Skeptic!")
            raise AssertionError(f"Unexpected role {role}")

        with tempfile.TemporaryDirectory() as tmp:
            cfg = OrchestratorConfig(
                project_dir=PROJECT_DIR,
                enable_skeptic=False,
                max_rounds=1,
                n_brainstormers=1,
                ledger_path=Path(tmp) / "l.json",
            )
            job = Job(problem="Prove dimensional lifting using a false sub-lemma.")
            await Orchestrator(job, ScriptedLLM(handler), self.verifier, cfg).run()
            self.assertEqual(job.status, JobStatus.EXHAUSTED)
            ev_types = [e.type for e in job.events]
            self.assertIn("lemma_refuted", ev_types)

    async def test_benchmark_suite_passes_all_entries(self) -> None:
        suite = PROJECT_DIR / "benchmarks" / "hj_suite.jsonl"
        results, all_ok = await run_benchmark_suite(PROJECT_DIR, suite, live_llm=False)
        self.assertTrue(all_ok, results)
        self.assertEqual(len(results), 12)

    def test_cli_audit_repo_and_index(self) -> None:
        rc_idx = cli_main(["--project-dir", str(PROJECT_DIR), "index", "--query", "HJUpper"])
        self.assertEqual(rc_idx, 0)
        rc_audit = cli_main(["--project-dir", str(PROJECT_DIR), "audit-repo"])
        self.assertEqual(rc_audit, 0)


if __name__ == "__main__":
    unittest.main()
