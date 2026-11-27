"""Zero-dependency JSON-RPC 2.0 stdio MCP server exposing brigade as a daily Antigravity toolset."""

from __future__ import annotations

import asyncio
import json
from pathlib import Path
import sys
from typing import Any

from . import blueprint, density_hj, explorer, hypergraph, skeptic_hj
from .explorer import ResearchLab
from .lean_verifier import RealLeanVerifier, lint_proof
from .library_index import PremiseIndex


TOOLS_SPEC: list[dict[str, Any]] = [
    {
        "name": "brigade_search_premises",
        "description": "Search precompiled Lean 4 theorems, definitions, and lemmas in HJBrigade.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "query": {"type": "string", "description": "Keyword or theorem signature tokens"},
                "limit": {"type": "integer", "default": 12},
            },
            "required": ["query"],
        },
    },
    {
        "name": "brigade_blueprint",
        "description": "Inspect a Lean 4 draft file: extract elaborated `⊢` goal states for every `sorry`, matching HJBrigade premises, and axiom status.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "file_path": {"type": "string", "description": "Path to .lean draft file (relative to project_dir or absolute)"},
            },
            "required": ["file_path"],
        },
    },
    {
        "name": "brigade_verify_snippet",
        "description": "Compile a Lean 4 snippet against HJBrigade, enforce I4 static lint, and optionally run `#print axioms`.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "code": {"type": "string", "description": "Lean 4 code snippet"},
                "theorem": {"type": "string", "default": "", "description": "Optional theorem name for #print axioms audit"},
                "imports": {"type": "array", "items": {"type": "string"}, "default": ["HJBrigade"]},
                "namespace": {"type": "string", "default": "HJBrigade"},
            },
            "required": ["code"],
        },
    },
    {
        "name": "brigade_certify",
        "description": "Solve finite Ramsey-family problems (hj, vdw, schur, ramsey, dhj, moser) and emit kernel-checked Lean 4 certificates or witnesses.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "family": {"type": "string", "enum": ["hj", "vdw", "schur", "ramsey", "dhj", "moser"]},
                "d": {"type": "integer"},
                "n": {"type": "integer"},
                "k": {"type": "integer", "default": 3},
                "r": {"type": "integer", "default": 2},
                "s": {"type": "integer", "default": 3},
                "t": {"type": "integer"},
                "theorem": {"type": "string", "default": ""},
                "verify": {"type": "boolean", "default": False},
            },
            "required": ["family"],
        },
    },
    {
        "name": "brigade_explore",
        "description": "Sweep a Ramsey parameter range (hj, vdw, schur, ramsey, dhj, moser) and analyze witness structure (symmetry, periodicity, certificate size).",
        "inputSchema": {
            "type": "object",
            "properties": {
                "family": {"type": "string", "enum": ["hj", "vdw", "schur", "ramsey", "dhj", "moser"]},
                "k": {"type": "integer", "default": 3},
                "r": {"type": "integer", "default": 2},
                "s": {"type": "integer", "default": 3},
                "t": {"type": "integer"},
                "start": {"type": "integer", "default": 1},
                "stop": {"type": "integer", "default": 6},
            },
            "required": ["family"],
        },
    },
    {
        "name": "brigade_audit_repo",
        "description": "Audit HJBrigade theorems against I1-I4 soundness invariants and `#print axioms`.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "module": {"type": "string", "default": "", "description": "Optional single module name filter"},
            },
        },
    },
    {
        "name": "brigade_lab_note",
        "description": "List or record verified theorems and open problems in research/DISCOVERIES.md and research/notes.jsonl.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "action": {"type": "string", "enum": ["list", "add"], "default": "list"},
                "family": {"type": "string", "default": ""},
                "title": {"type": "string", "default": ""},
                "status": {"type": "string", "default": "VERIFIED"},
                "summary": {"type": "string", "default": ""},
                "theorem": {"type": "string", "default": ""},
                "evidence": {"type": "string", "default": ""},
            },
        },
    },
]


class MCPServer:
    """In-process and stdio JSON-RPC 2.0 handler for brigade tools."""

    def __init__(self, project_dir: Path | str):
        self.project_dir = Path(project_dir).resolve()
        self.index = PremiseIndex(self.project_dir)
        self.verifier = RealLeanVerifier(self.project_dir, timeout_s=60.0)
        self.lab = ResearchLab(self.project_dir)

    async def handle_request(self, req: dict[str, Any]) -> dict[str, Any] | None:
        method = req.get("method", "")
        req_id = req.get("id")
        params = req.get("params") or {}

        # Notifications have no id and expect no JSON-RPC response
        if method.startswith("notifications/"):
            return None

        if method == "initialize":
            return _ok(
                req_id,
                {
                    "protocolVersion": "2024-11-05",
                    "capabilities": {"tools": {}},
                    "serverInfo": {"name": "brigade-ramsey-mcp", "version": "0.2.0"},
                },
            )
        if method == "ping":
            return _ok(req_id, {})
        if method == "tools/list":
            return _ok(req_id, {"tools": TOOLS_SPEC})
        if method == "tools/call":
            name = params.get("name", "")
            args = params.get("arguments") or {}
            try:
                payload = await self._call_tool(name, args)
                return _ok(
                    req_id,
                    {
                        "content": [{"type": "text", "text": json.dumps(payload, indent=2, ensure_ascii=False)}],
                        "isError": False,
                    },
                )
            except Exception as exc:
                return _ok(
                    req_id,
                    {
                        "content": [{"type": "text", "text": json.dumps({"error": str(exc)}, indent=2)}],
                        "isError": True,
                    },
                )
        if req_id is None:
            return None
        return {
            "jsonrpc": "2.0",
            "id": req_id,
            "error": {"code": -32601, "message": f"Method not found: {method}"},
        }

    async def _call_tool(self, name: str, args: dict[str, Any]) -> dict[str, Any]:
        if name == "brigade_search_premises":
            self.index.refresh()
            hits = self.index.search(str(args.get("query", "")), limit=int(args.get("limit", 12)))
            return {
                "count": len(hits),
                "hits": [
                    {
                        "module": e.module,
                        "kind": e.kind,
                        "name": e.name,
                        "line": e.line,
                        "signature": e.signature,
                        "doc": e.doc,
                    }
                    for e in hits
                ],
            }

        if name == "brigade_blueprint":
            raw_path = Path(str(args["file_path"]))
            target = raw_path if raw_path.is_absolute() else (self.project_dir / raw_path)
            return await blueprint.inspect_blueprint(self.project_dir, target.resolve())

        if name == "brigade_verify_snippet":
            code = str(args["code"])
            lint = lint_proof(code)
            if lint:
                return {"ok": False, "lint_errors": lint, "errors": lint}
            imports = args.get("imports", ["HJBrigade"])
            namespace = args.get("namespace", "HJBrigade")
            chk = await self.verifier.check(code, imports=imports, namespace=namespace)
            out: dict[str, Any] = {
                "ok": chk.ok and chk.sorries == 0,
                "sorries": chk.sorries,
                "errors": chk.errors,
                "warnings": chk.warnings,
                "elapsed_s": chk.elapsed_s,
            }
            thm = str(args.get("theorem", "")).strip()
            if chk.ok and chk.sorries == 0 and thm:
                aud = await self.verifier.axiom_audit(code, thm, imports=imports, namespace=namespace)
                out["axiom_audit"] = {"ok": aud.ok, "axioms": aud.axioms, "note": aud.note}
                out["ok"] = out["ok"] and aud.ok
            return out

        if name == "brigade_certify":
            return await self._tool_certify(args)

        if name == "brigade_explore":
            fam = str(args["family"])
            t_arg = args.get("t")
            rows = explorer.explore_family(
                fam,
                k=int(args.get("k", 3)),
                r=int(args.get("r", 2)),
                s=int(args.get("s", 3)),
                t=int(t_arg) if t_arg is not None else None,
                start=int(args.get("start", 1)),
                stop=int(args.get("stop", 6)),
            )
            return {"family": fam, "rows": rows}

        if name == "brigade_audit_repo":
            self.index.refresh()
            mod_filter = str(args.get("module", "")).strip()
            by_mod: dict[str, list[str]] = {}
            for e in self.index.entries:
                if e.kind in ("theorem", "lemma") and (not mod_filter or e.module == mod_filter):
                    by_mod.setdefault(e.module, []).append(e.name)
            passed = 0
            failed: list[dict[str, Any]] = []
            for mod, names in sorted(by_mod.items()):
                path = self.project_dir.joinpath(*mod.split(".")).with_suffix(".lean")
                lint = lint_proof(path.read_text(encoding="utf-8"))
                if lint:
                    failed.append({"module": mod, "lint": lint})
                    continue
                audits = await self.verifier.audit_existing_module(mod, names)
                for aud in audits:
                    if aud.ok:
                        passed += 1
                    else:
                        failed.append(
                            {
                                "module": mod,
                                "theorem": aud.theorem_name,
                                "axioms": aud.axioms,
                                "note": aud.note,
                            }
                        )
            return {
                "modules": len(by_mod),
                "total": passed + len(failed),
                "passed": passed,
                "failed": failed,
            }

        if name == "brigade_lab_note":
            action = str(args.get("action", "list"))
            fam = str(args.get("family", "")).strip() or None
            if action == "add":
                note = self.lab.add_note(
                    title=str(args.get("title", "Untitled note")),
                    family=fam or "general",
                    status=str(args.get("status", "VERIFIED")),
                    summary=str(args.get("summary", "")),
                    theorem=str(args.get("theorem", "")),
                    evidence=str(args.get("evidence", "")),
                )
                return {"added": note, "markdown_path": str(self.lab.markdown_path)}
            return {"notes": self.lab.list_notes(family=fam)}

        raise ValueError(f"Unknown MCP tool: {name!r}")

    async def _tool_certify(self, args: dict[str, Any]) -> dict[str, Any]:
        fam = str(args["family"]).lower().strip()
        thm = str(args.get("theorem", "")).strip() or None
        verify = bool(args.get("verify", False))
        lean_src = ""
        thm_name = thm or ""
        meta: dict[str, Any] = {"family": fam}

        if fam == "hj":
            d = int(args.get("d", 4))
            k = int(args.get("k", 3))
            r = int(args.get("r", 2))
            res = skeptic_hj.solve_hj(d, k, r)
            meta.update({"status": res.status, "nodes": res.nodes_explored})
            if res.status == "SAT_LINE_FREE":
                thm_name = thm or f"hj_{k}_{r}_gt_{d}"
                lean_src = skeptic_hj.emit_lower_bound_lean(res, theorem_name=thm_name)
            elif res.status == "UNSAT_MONO_FORCED":
                thm_name = thm or f"hj_{k}_{r}_le_{d}"
                lean_src = skeptic_hj.emit_upper_bound_lean(res, theorem_name=thm_name)
        elif fam == "vdw":
            n = int(args.get("n", args.get("N", 9)))
            k = int(args.get("k", 3))
            r = int(args.get("r", 2))
            res = hypergraph.solve_vdw_cert(n, k, r)
            meta.update({"status": res.status, "nodes": res.nodes_explored, "structure": res.structure})
            if res.status in ("UNSAT_MONO", "SAT_FREE"):
                thm_name = thm or (f"vdw_{k}_{r}_le_{n}" if res.status == "UNSAT_MONO" else f"vdw_{k}_{r}_gt_{n}")
                lean_src = hypergraph.emit_vdw_cert_lean(res, theorem_name=thm_name)
        elif fam == "schur":
            n = int(args.get("n", args.get("N", 5)))
            r = int(args.get("r", 2))
            res = hypergraph.solve_schur(n, r)
            meta.update({"status": res.status, "nodes": res.nodes_explored, "structure": res.structure})
            if res.status in ("UNSAT_MONO", "SAT_FREE"):
                thm_name = thm or (f"schur_{r}_le_{n}" if res.status == "UNSAT_MONO" else f"schur_{r}_gt_{n}")
                lean_src = hypergraph.emit_schur_lean(res, theorem_name=thm_name)
        elif fam == "ramsey":
            n = int(args.get("n", args.get("N", 5)))
            s = int(args.get("s", 3))
            t = args.get("t")
            r = int(args.get("r", 2))
            res = hypergraph.solve_graph_ramsey(n, s, int(t) if t is not None else None, r=r)
            meta.update({"status": res.status, "notes": res.notes})
            if res.status == "SAT_FREE":
                thm_name = thm or f"ramsey_{s}_{t or s}_gt_{n}"
                lean_src = hypergraph.emit_graph_ramsey_lower_lean(res, theorem_name=thm_name)
        elif fam == "dhj":
            d = int(args.get("d", 4))
            k = int(args.get("k", 3))
            dres = density_hj.solve_dhj(d, k)
            thm_name = thm or f"dhj_{d}_{k}_ge_{dres.size}"
            lean_src = density_hj.emit_dhj_lower_lean(dres, theorem_name=thm_name)
            meta.update({"status": "WITNESS", "size": dres.size, "optimal": dres.optimal})
        elif fam == "moser":
            d = int(args.get("d", 3))
            mres = density_hj.solve_moser(d)
            thm_name = thm or f"moser_{d}_3_ge_{mres.size}"
            lean_src = density_hj.emit_moser_lower_lean(mres, theorem_name=thm_name)
            meta.update({"status": "WITNESS", "size": mres.size, "optimal": mres.optimal})
        else:
            raise ValueError(f"Unsupported certification family: {fam!r}")

        meta["theorem"] = thm_name
        meta["lean"] = lean_src
        if verify and lean_src and thm_name:
            chk = await self.verifier.check(lean_src)
            aud = await self.verifier.axiom_audit(lean_src, thm_name)
            meta["verified"] = chk.ok and chk.sorries == 0 and aud.ok
            meta["axioms"] = aud.axioms
        return meta


def _ok(req_id: Any, result: dict[str, Any]) -> dict[str, Any]:
    return {"jsonrpc": "2.0", "id": req_id, "result": result}


def _read_message(stream: Any) -> tuple[dict[str, Any] | None, str]:
    """Read either a Content-Length framed or newline-delimited JSON-RPC message."""
    while True:
        raw_line = stream.readline()
        if not raw_line:
            return None, "ndjson"
        if isinstance(raw_line, str):
            line = raw_line.strip()
        else:
            line = raw_line.decode("utf-8", errors="replace").strip()
        if not line:
            continue
        if line.lower().startswith("content-length:"):
            length = int(line.split(":", 1)[1].strip())
            while True:
                hdr = stream.readline()
                if not hdr or hdr.strip() in (b"", ""):
                    break
            body = stream.read(length)
            text = body.decode("utf-8", errors="replace") if isinstance(body, bytes) else body
            return json.loads(text), "lsp"
        return json.loads(line), "ndjson"


def _write_message(stream: Any, msg: dict[str, Any], framing: str) -> None:
    payload = json.dumps(msg, ensure_ascii=False)
    if framing == "lsp":
        data = payload.encode("utf-8")
        out = f"Content-Length: {len(data)}\r\n\r\n".encode("ascii") + data
        stream.write(out)
    else:
        stream.write((payload + "\n").encode("utf-8"))
    stream.flush()


async def serve_stdio(project_dir: Path | str) -> int:
    server = MCPServer(project_dir)
    stdin_buf = sys.stdin.buffer
    stdout_buf = sys.stdout.buffer
    while True:
        req, framing = _read_message(stdin_buf)
        if req is None:
            return 0
        resp = await server.handle_request(req)
        if resp is not None:
            _write_message(stdout_buf, resp, framing)


def run_stdio_server(project_dir: Path | str) -> int:
    return asyncio.run(serve_stdio(project_dir))
