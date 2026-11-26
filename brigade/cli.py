"""Command-line interface for hj-brigade."""

from __future__ import annotations

import argparse
import asyncio
import json
from pathlib import Path
import re
import sys

from . import bench, blueprint, density_hj, skeptic_hj
from .lean_verifier import RealLeanVerifier, lint_proof
from .library_index import PremiseIndex
from .llm import MultiProviderLLM, ProviderConfig
from .models import Job
from .orchestrator import Orchestrator, OrchestratorConfig


def _default_project_dir() -> Path:
    return Path(__file__).resolve().parent.parent


async def _cmd_verify(args: argparse.Namespace) -> int:
    proj = Path(args.project_dir).resolve()
    verifier = RealLeanVerifier(proj)
    src = Path(args.file).read_text(encoding="utf-8")
    lint = lint_proof(src)
    if lint:
        print(f"LINT FAILED (I4): {lint}")
        return 2
    res = await verifier.check(src, imports=args.imports, namespace=args.namespace)
    print(res.summary())
    if not res.ok:
        for err in res.errors:
            print(f"  ERROR: {err}")
        return 1
    if res.sorries > 0:
        print(f"REJECTED (I1): {res.sorries} sorry(ies) present")
        return 1
    if args.theorem:
        audit = await verifier.axiom_audit(src, args.theorem, imports=args.imports, namespace=args.namespace)
        print(f"AXIOM AUDIT ({args.theorem}): ok={audit.ok} axioms={audit.axioms} {audit.note}")
        return 0 if audit.ok else 1
    return 0


async def _cmd_audit_repo(args: argparse.Namespace) -> int:
    proj = Path(args.project_dir).resolve()
    verifier = RealLeanVerifier(proj)
    idx = PremiseIndex(proj)
    theorems = [e for e in idx.entries if e.kind in ("theorem", "lemma")]
    by_mod: dict[str, list[str]] = {}
    for e in theorems:
        by_mod.setdefault(e.module, []).append(e.name)

    total = 0
    failed = 0
    for mod, names in sorted(by_mod.items()):
        path = proj.joinpath(*mod.split(".")).with_suffix(".lean")
        lint = lint_proof(path.read_text(encoding="utf-8"))
        if lint:
            print(f"[FAIL-LINT] {mod}: {lint}")
            failed += len(names)
            total += len(names)
            continue
        audits = await verifier.audit_existing_module(mod, names)
        for aud in audits:
            total += 1
            tag = "PASS" if aud.ok else "FAIL"
            ax = ", ".join(aud.axioms) if aud.axioms else "none"
            print(f"[{tag}] {mod}.{aud.theorem_name}  axioms=[{ax}] {aud.note}")
            if not aud.ok:
                failed += 1
    print(f"\nAudited {total} theorem(s) across {len(by_mod)} module(s): {total - failed} passed, {failed} failed.")
    return 0 if failed == 0 else 1


async def _cmd_certify_hj(args: argparse.Namespace) -> int:
    proj = Path(args.project_dir).resolve()
    res = skeptic_hj.solve_hj(
        args.d, args.k, args.r, max_nodes=args.max_nodes, time_limit_s=args.time_limit
    )
    print(
        f"HJ({args.k}, {args.r}) @ d={args.d}: status={res.status}, "
        f"words={res.num_words}, lines={res.num_lines}, nodes={res.nodes_explored}, time={res.elapsed_s:.3f}s"
    )
    if res.status == "UNKNOWN":
        return 2
    if res.status == "SAT_LINE_FREE":
        thm = args.theorem or f"hj_{args.k}_{args.r}_gt_{args.d}"
        lean_src = skeptic_hj.emit_lower_bound_lean(res, theorem_name=thm)
    else:
        thm = args.theorem or f"hj_{args.k}_{args.r}_le_{args.d}"
        lean_src = skeptic_hj.emit_upper_bound_lean(res, theorem_name=thm)

    if args.out:
        out_path = Path(args.out)
        out_path.write_text("import HJBrigade\n\nnamespace HJBrigade\n\n" + lean_src + "\nend HJBrigade\n", encoding="utf-8")
        print(f"Wrote certificate to {out_path}")

    if args.verify:
        verifier = RealLeanVerifier(proj, timeout_s=args.lean_timeout)
        chk = await verifier.check(lean_src)
        aud = await verifier.axiom_audit(lean_src, thm)
        print(f"Lean verification: {chk.summary()}")
        print(f"Axiom audit ({thm}): ok={aud.ok} axioms={aud.axioms} {aud.note}")
        return 0 if (chk.ok and chk.sorries == 0 and aud.ok) else 1
    return 0


def _cmd_index(args: argparse.Namespace) -> int:
    idx = PremiseIndex(Path(args.project_dir).resolve())
    hits = idx.search(args.query or "", limit=args.limit)
    for e in hits:
        print(f"[{e.module}:{e.line}] {e.signature}")
    return 0


async def _cmd_prove(args: argparse.Namespace) -> int:
    proj = Path(args.project_dir).resolve()
    verifier = RealLeanVerifier(proj)
    llm = MultiProviderLLM(ProviderConfig.from_env())
    cfg = OrchestratorConfig(
        project_dir=proj,
        max_rounds=args.rounds,
        prove_samples=args.samples,
    )
    job = Job(problem=args.problem)
    orch = Orchestrator(job, llm, verifier, cfg)
    await orch.run()
    print(f"Status: {job.status.value}")
    print(f"Summary: {job.summary}")
    if job.final_lean:
        print("\n--- Verified Lean Output ---")
        print(job.final_lean)
    if args.json:
        print(json.dumps({"status": job.status.value, "summary": job.summary, "lean_calls": job.lean_calls, "llm_calls": job.llm_calls}, indent=2))
    return 0 if job.status.value in ("proved", "refuted") else 1


async def _cmd_bench(args: argparse.Namespace) -> int:
    proj = Path(args.project_dir).resolve()
    suite = Path(args.suite) if args.suite else (proj / "benchmarks" / "hj_suite.jsonl")
    results, all_ok = await bench.run_benchmark_suite(proj, suite, live_llm=args.live)
    for r in results:
        tag = "PASS" if r["passed"] else "FAIL"
        print(
            f"[{tag}] {r['id']:<20} expected={r['expected']:<8} actual={r['actual']:<8} "
            f"lean={r['lean_calls']} llm={r['llm_calls']} ({r['elapsed_s']:.2f}s)"
        )
    if args.json:
        print(json.dumps(results, indent=2))
    passed_cnt = sum(1 for r in results if r["passed"])
    print(f"\nBenchmark suite: {passed_cnt}/{len(results)} passed.")
    return 0 if all_ok else 1


async def _cmd_certify_dhj(args: argparse.Namespace) -> int:
    proj = Path(args.project_dir).resolve()
    res = density_hj.solve_dhj(args.d, args.k, restarts=args.restarts, steps=args.steps)
    print(
        f"DHJ(d={args.d}, k={args.k}): max_found={res.size}/{res.num_words} "
        f"(optimal={res.optimal}, time={res.elapsed_s:.3f}s)"
    )
    thm = args.theorem or f"dhj_{args.d}_{args.k}_ge_{res.size}"
    lean_src = density_hj.emit_dhj_lower_lean(res, theorem_name=thm)
    if args.out:
        out_path = Path(args.out)
        out_path.write_text(
            "import HJBrigade\n\nnamespace HJBrigade\n\n" + lean_src + "\nend HJBrigade\n",
            encoding="utf-8",
        )
        print(f"Wrote density witness to {out_path}")
    if args.verify:
        verifier = RealLeanVerifier(proj, timeout_s=args.lean_timeout)
        chk = await verifier.check(lean_src)
        aud = await verifier.axiom_audit(lean_src, thm)
        print(f"Lean verification: {chk.summary()}")
        print(f"Axiom audit ({thm}): ok={aud.ok} axioms={aud.axioms} {aud.note}")
        return 0 if (chk.ok and chk.sorries == 0 and aud.ok) else 1
    return 0


async def _cmd_blueprint(args: argparse.Namespace) -> int:
    proj = Path(args.project_dir).resolve()
    report = await blueprint.inspect_blueprint(proj, Path(args.file).resolve())
    if args.json:
        print(json.dumps(report, indent=2))
        return 0 if report["compile_ok"] else 1
    print(
        f"Blueprint {report['file']}: compile_ok={report['compile_ok']} "
        f"({report['completed_count']} completed, {report['open_count']} open sorry)"
    )
    for err in report["errors"]:
        print(f"  ERROR: {err}")
    for item in report["items"]:
        if item["has_sorry"]:
            print(f"\n[OPEN] {item['name']} (L{item['lines'][0]}-{item['lines'][1]})")
            for g in item["goals"]:
                print(f"  Goal:\n    " + g.replace("\n", "\n    "))
            if item["premise_hints"]:
                print("  Top HJBrigade premises:")
                for h in item["premise_hints"]:
                    print(f"    - {h}")
        else:
            status = "PASS" if item["axiom_ok"] else ("DEFERRED" if item["axiom_ok"] is None else "FAIL")
            print(f"[{status}] {item['name']}  axioms={item['axioms']} {item['note']}")
    return 0 if report["compile_ok"] else 1


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(prog="hj-brigade", description="Neuro-symbolic Lean 4 Ramsey / Hales-Jewett prover")
    p.add_argument("--project-dir", default=str(_default_project_dir()), help="Path to HJBrigade Lake project")
    sub = p.add_subparsers(dest="cmd", required=True)

    pv = sub.add_parser("verify", help="Verify a Lean file and optionally audit a theorem's axioms")
    pv.add_argument("file")
    pv.add_argument("--theorem", default="")
    pv.add_argument("--imports", nargs="*", default=["HJBrigade"])
    pv.add_argument("--namespace", default="HJBrigade")

    sub.add_parser("audit-repo", help="Audit axioms of all theorems in HJBrigade")

    pc = sub.add_parser("certify-hj", help="Solve finite HJ(k, r) at dimension d and emit Lean 4 certificate")
    pc.add_argument("--d", type=int, required=True)
    pc.add_argument("--k", type=int, required=True)
    pc.add_argument("--r", type=int, required=True)
    pc.add_argument("--theorem", default="")
    pc.add_argument("--out", default="")
    pc.add_argument("--verify", action="store_true", help="Compile & axiom-audit certificate with Lean 4")
    pc.add_argument("--max-nodes", type=int, default=500_000)
    pc.add_argument("--time-limit", type=float, default=20.0)
    pc.add_argument("--lean-timeout", type=float, default=60.0)

    pi = sub.add_parser("index", help="Search precompiled HJBrigade theorems and definitions")
    pi.add_argument("--query", default="")
    pi.add_argument("--limit", type=int, default=15)

    pp = sub.add_parser("prove", help="Run the full proving brigade on a Ramsey/HJ claim")
    pp.add_argument("problem")
    pp.add_argument("--rounds", type=int, default=3)
    pp.add_argument("--samples", type=int, default=2)
    pp.add_argument("--json", action="store_true")

    pb = sub.add_parser("bench", help="Run the Ramsey/HJ benchmark suite against real Lean 4")
    pb.add_argument("--suite", default="")
    pb.add_argument("--live", action="store_true", help="Enable live LLM calls from env keys")
    pb.add_argument("--json", action="store_true")

    pd = sub.add_parser("certify-dhj", help="Find and Lean-verify line-free density lower bounds in [k]^d")
    pd.add_argument("--d", type=int, required=True)
    pd.add_argument("--k", type=int, required=True)
    pd.add_argument("--theorem", default="")
    pd.add_argument("--out", default="")
    pd.add_argument("--verify", action="store_true")
    pd.add_argument("--restarts", type=int, default=30)
    pd.add_argument("--steps", type=int, default=1200)
    pd.add_argument("--lean-timeout", type=float, default=60.0)

    pbl = sub.add_parser("blueprint", help="Extract sorry goals, premise hints, and axiom status for a Lean file")
    pbl.add_argument("file")
    pbl.add_argument("--json", action="store_true")
    return p


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    if args.cmd == "index":
        return _cmd_index(args)
    coro_map = {
        "verify": _cmd_verify,
        "audit-repo": _cmd_audit_repo,
        "certify-hj": _cmd_certify_hj,
        "certify-dhj": _cmd_certify_dhj,
        "blueprint": _cmd_blueprint,
        "prove": _cmd_prove,
        "bench": _cmd_bench,
    }
    return asyncio.run(coro_map[args.cmd](args))


if __name__ == "__main__":
    sys.exit(main())
