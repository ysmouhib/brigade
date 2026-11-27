"""Tests for Graph Ramsey, Schur, HyperCert certificates, explorer sweeps, ResearchLab, and MCP server."""

from __future__ import annotations

import json
from pathlib import Path
import tempfile
import unittest

from brigade import explorer, hypergraph
from brigade.cli import main as cli_main
from brigade.explorer import ResearchLab
from brigade.lean_verifier import RealLeanVerifier
from brigade.llm import ScriptedLLM
from brigade.mcp_server import MCPServer
from brigade.models import Job, JobStatus
from brigade.orchestrator import Orchestrator, OrchestratorConfig

PROJECT_DIR = Path(__file__).resolve().parent.parent


class TestRamseySchurAndWorkbench(unittest.IsolatedAsyncioTestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.verifier = RealLeanVerifier(PROJECT_DIR, timeout_s=60.0)

    def test_hypergraph_schur_and_vdw_solvers_and_python_verification(self) -> None:
        s4 = hypergraph.solve_schur(4, 2)
        self.assertEqual(s4.status, "SAT_FREE")
        self.assertIsNotNone(s4.witness_coloring)

        s5 = hypergraph.solve_schur(5, 2)
        self.assertEqual(s5.status, "UNSAT_MONO")
        self.assertIsNotNone(s5.cert_tree)
        triples5, _ = hypergraph.schur_hyperedges(5)
        self.assertTrue(
            hypergraph.verify_hyper_cert(5, 2, set(triples5), s5.cert_tree, {0: 0})
        )

        w9 = hypergraph.solve_vdw_cert(9, 3, 2, root=4)
        self.assertEqual(w9.status, "UNSAT_MONO")
        self.assertIsNotNone(w9.cert_tree)
        pairs9, edges9 = hypergraph.vdw_hyperedges(9, 3)
        self.assertTrue(
            hypergraph.verify_hyper_cert(9, 2, dict(zip(pairs9, edges9)), w9.cert_tree, {4: 0})
        )

    async def test_emitted_ramsey_schur_vdw_certificates_verify_in_real_lean(self) -> None:
        # Graph Ramsey witness with digits '0'/'1' in theorem name tests bool table safety
        ram = hypergraph.solve_graph_ramsey(8, 3, 4)
        self.assertEqual(ram.status, "SAT_FREE")
        lean_ram = hypergraph.emit_graph_ramsey_lower_lean(ram, theorem_name="test_r01_3_4_gt_8")
        self.assertIn("private_graph_test_r01_3_4_gt_8_table", lean_ram)
        chk = await self.verifier.check(lean_ram)
        self.assertTrue(chk.ok and chk.sorries == 0, chk.errors)
        aud = await self.verifier.axiom_audit(lean_ram, "test_r01_3_4_gt_8")
        self.assertTrue(aud.ok, aud.note)

        # Schur certificate S(2) = 5 in real Lean
        s5 = hypergraph.solve_schur(5, 2)
        lean_schur = hypergraph.emit_schur_lean(s5, theorem_name="test_schur_2_le_5")
        chk_s = await self.verifier.check(lean_schur)
        self.assertTrue(chk_s.ok and chk_s.sorries == 0, chk_s.errors)
        aud_s = await self.verifier.axiom_audit(lean_schur, "test_schur_2_le_5")
        self.assertTrue(aud_s.ok, aud_s.note)

        # VdW HyperCert certificate W(3,2) = 9 in real Lean
        w9 = hypergraph.solve_vdw_cert(9, 3, 2, root=4)
        lean_vdw = hypergraph.emit_vdw_cert_lean(w9, theorem_name="test_vdw_3_2_le_9")
        chk_v = await self.verifier.check(lean_vdw)
        self.assertTrue(chk_v.ok and chk_v.sorries == 0, chk_v.errors)
        aud_v = await self.verifier.axiom_audit(lean_vdw, "test_vdw_3_2_le_9")
        self.assertTrue(aud_v.ok, aud_v.note)

    def test_explorer_sweeps_and_research_lab_persistence(self) -> None:
        schur_rows = explorer.explore_family("schur", r=2, start=3, stop=5)
        self.assertEqual([r["status"] for r in schur_rows], ["SAT_FREE", "SAT_FREE", "UNSAT_MONO"])

        ramsey_rows = explorer.explore_family("ramsey", s=3, t=3, start=4, stop=5)
        self.assertTrue(all(r["status"] == "SAT_FREE" for r in ramsey_rows))

        with tempfile.TemporaryDirectory() as tmp:
            lab = ResearchLab(tmp)
            note = lab.add_note(
                title="Test discovery",
                family="schur",
                status="VERIFIED",
                summary="S(2)=5 verified in Lean",
                theorem="schur_2_exact",
            )
            self.assertEqual(note["id"], 1)
            self.assertEqual(len(lab.list_notes(family="schur")), 1)
            self.assertIn("schur_2_exact", lab.markdown_path.read_text(encoding="utf-8"))

    async def test_mcp_server_protocol_and_tools(self) -> None:
        server = MCPServer(PROJECT_DIR)
        init_resp = await server.handle_request({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {}})
        assert init_resp is not None
        self.assertEqual(init_resp["result"]["serverInfo"]["name"], "brigade-ramsey-mcp")

        tools_resp = await server.handle_request({"jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {}})
        assert tools_resp is not None
        names = {t["name"] for t in tools_resp["result"]["tools"]}
        self.assertEqual(
            names,
            {
                "brigade_search_premises",
                "brigade_blueprint",
                "brigade_verify_snippet",
                "brigade_certify",
                "brigade_explore",
                "brigade_audit_repo",
                "brigade_lab_note",
            },
        )

        search_resp = await server.handle_request(
            {
                "jsonrpc": "2.0",
                "id": 3,
                "method": "tools/call",
                "params": {"name": "brigade_search_premises", "arguments": {"query": "ramsey_4_4_exact", "limit": 3}},
            }
        )
        assert search_resp is not None
        payload = json.loads(search_resp["result"]["content"][0]["text"])
        self.assertTrue(any(h["name"] == "ramsey_4_4_exact" for h in payload["hits"]))

        cert_resp = await server.handle_request(
            {
                "jsonrpc": "2.0",
                "id": 4,
                "method": "tools/call",
                "params": {"name": "brigade_certify", "arguments": {"family": "schur", "n": 5, "r": 2, "verify": True}},
            }
        )
        assert cert_resp is not None
        cert_payload = json.loads(cert_resp["result"]["content"][0]["text"])
        self.assertTrue(cert_payload["verified"], cert_payload)

    async def test_orchestrator_schur_and_ramsey_zero_llm_fastpaths(self) -> None:
        def fail_if_called(role: str, _sys: str, _usr: str):
            raise AssertionError(f"Unexpected LLM call ({role}) for fastpath query")

        with tempfile.TemporaryDirectory() as tmp:
            cfg = OrchestratorConfig(project_dir=PROJECT_DIR, ledger_path=Path(tmp) / "l.json")

            job_schur = Job(problem="Prove HasMonoSchur 5 2")
            await Orchestrator(job_schur, ScriptedLLM(fail_if_called), self.verifier, cfg).run()
            self.assertEqual(job_schur.status, JobStatus.PROVED)

            job_ram = Job(problem="Prove GraphRamseyUpper 8 3 4")
            await Orchestrator(job_ram, ScriptedLLM(fail_if_called), self.verifier, cfg).run()
            self.assertEqual(job_ram.status, JobStatus.REFUTED)
            self.assertIsNotNone(job_ram.refutation)
            assert job_ram.refutation is not None
            self.assertTrue(job_ram.refutation.lean_verified)

    def test_cli_new_subcommands(self) -> None:
        self.assertEqual(cli_main(["--project-dir", str(PROJECT_DIR), "explore", "schur", "--r", "2", "--start", "4", "--stop", "5", "--json"]), 0)
        self.assertEqual(cli_main(["--project-dir", str(PROJECT_DIR), "lab", "list"]), 0)
        self.assertEqual(cli_main(["--project-dir", str(PROJECT_DIR), "certify-schur", "--n", "5", "--r", "2"]), 0)
        self.assertEqual(cli_main(["--project-dir", str(PROJECT_DIR), "certify-ramsey", "--n", "8", "--s", "3", "--t", "4"]), 0)


if __name__ == "__main__":
    unittest.main()
