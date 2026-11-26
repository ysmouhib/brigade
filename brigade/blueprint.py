"""Interactive agent-native Lean blueprint inspector: goal extraction, premise hints, and axiom audits."""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
import re
from typing import Any

from .lean_verifier import RealLeanVerifier, lint_proof, strip_lean_comments
from .library_index import PremiseIndex

_THM_START_RE = re.compile(r"^(?:private\s+|protected\s+)?(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_.']*)\b")
_INFO_LOC_RE = re.compile(r"^[^:\n]+(?::[^:\n]+)*:(\d+):(\d+):\s*info:\s*(.*)$")
_ERR_LOC_RE = re.compile(r"^[^:\n]+(?::[^:\n]+)*:(\d+):(\d+):\s*error:\s*(.*)$")
_SORRY_TOKEN_RE = re.compile(r"\bsorry\b")


@dataclass
class BlueprintItem:
    name: str
    kind: str
    start_line: int
    end_line: int
    signature: str
    has_sorry: bool
    goals: list[str] = field(default_factory=list)
    premise_hints: list[str] = field(default_factory=list)
    axiom_ok: bool | None = None
    axioms: list[str] = field(default_factory=list)
    note: str = ""


def _parse_theorems(src: str) -> list[dict[str, Any]]:
    lines = src.splitlines()
    clean_lines = strip_lean_comments(src).splitlines()
    blocks: list[dict[str, Any]] = []
    cur: dict[str, Any] | None = None

    for idx, line in enumerate(lines, start=1):
        clean_stripped = (clean_lines[idx - 1] if idx - 1 < len(clean_lines) else "").strip()
        m = _THM_START_RE.match(clean_stripped)
        if m:
            if cur is not None:
                cur["end_line"] = idx - 1
                blocks.append(cur)
            cur = {
                "kind": m.group(1),
                "name": m.group(2),
                "start_line": idx,
                "end_line": len(lines),
            }
        elif clean_stripped.startswith(("def ", "abbrev ", "structure ", "inductive ", "end ")) and cur is not None:
            cur["end_line"] = idx - 1
            blocks.append(cur)
            cur = None

    if cur is not None:
        blocks.append(cur)

    for b in blocks:
        s, e = b["start_line"] - 1, b["end_line"]
        chunk = "\n".join(lines[s:e])
        clean_chunk = "\n".join(clean_lines[s:e])
        b["text"] = chunk
        b["signature"] = " ".join(clean_chunk.split(":=")[0].split())
        b["has_sorry"] = bool(_SORRY_TOKEN_RE.search(clean_chunk))
    return blocks


def _inject_trace_state(src: str) -> tuple[str, dict[int, int]]:
    """Replace code `sorry` tokens with `trace_state` + `sorry`, ignoring comments/docstrings."""
    raw_lines = src.splitlines()
    clean_lines = strip_lean_comments(src).splitlines()
    out_lines: list[str] = []
    orig_line_for_injected: dict[int, int] = {}
    for idx, line in enumerate(raw_lines):
        orig_idx = idx + 1
        clean_line = clean_lines[idx] if idx < len(clean_lines) else ""
        if not _SORRY_TOKEN_RE.search(clean_line):
            out_lines.append(line)
            orig_line_for_injected[len(out_lines)] = orig_idx
            continue
        m_clean = re.match(r"^(\s*)sorry\b(.*)$", clean_line)
        if m_clean:
            m_raw = re.match(r"^(\s*)sorry\b(.*)$", line)
            indent = m_raw.group(1) if m_raw else m_clean.group(1)
            rest = m_raw.group(2) if m_raw else ""
            out_lines.append(f"{indent}trace_state")
            orig_line_for_injected[len(out_lines)] = orig_idx
            out_lines.append(f"{indent}sorry{rest}")
            orig_line_for_injected[len(out_lines)] = orig_idx
        else:
            m_pos = _SORRY_TOKEN_RE.search(clean_line)
            assert m_pos is not None
            patched = line[: m_pos.start()] + "(by trace_state; sorry)" + line[m_pos.end() :]
            out_lines.append(patched)
            orig_line_for_injected[len(out_lines)] = orig_idx
    return "\n".join(out_lines) + "\n", orig_line_for_injected


_SORRY_WARN_RE = re.compile(r"^[^:\n]+(?::[^:\n]+)*:(\d+):(\d+):\s*warning:\s*declaration uses [`']sorry[`']")


def _parse_located_goals(raw_output: str) -> list[tuple[int, str]]:
    goals: list[tuple[int, str]] = []
    cur_buf: list[str] = []
    explicit_line: int | None = None

    for line in raw_output.splitlines():
        if (m_sorry := _SORRY_WARN_RE.match(line)):
            if cur_buf and any("⊢" in ln for ln in cur_buf):
                goals.append((explicit_line or int(m_sorry.group(1)), "\n".join(cur_buf).strip()))
            cur_buf = []
            explicit_line = None
        elif (m_inf := _INFO_LOC_RE.match(line)):
            if cur_buf and any("⊢" in ln for ln in cur_buf) and explicit_line is not None:
                goals.append((explicit_line, "\n".join(cur_buf).strip()))
                cur_buf = []
            explicit_line = int(m_inf.group(1))
            if m_inf.group(3).strip():
                cur_buf.append(m_inf.group(3).strip())
        elif _ERR_LOC_RE.match(line) or re.match(r"^[^:\n]+(?::[^:\n]+)*:\d+:\d+:\s*warning:", line):
            cur_buf = []
            explicit_line = None
        elif line.strip():
            cur_buf.append(line.rstrip())
    if cur_buf and explicit_line is not None and any("⊢" in ln for ln in cur_buf):
        goals.append((explicit_line, "\n".join(cur_buf).strip()))
    return goals


async def inspect_blueprint(project_dir: Path, lean_file: Path) -> dict[str, Any]:
    """Analyze a Lean file: extract exact `⊢` goals for every `sorry`, retrieve `HJBrigade`
    premises, and `#print axioms` audit all completed theorems."""
    src = lean_file.read_text(encoding="utf-8")
    blocks = _parse_theorems(src)
    verifier = RealLeanVerifier(project_dir, timeout_s=60.0)
    index = PremiseIndex(project_dir)

    has_imports = any(line.lstrip().startswith("import ") for line in src.splitlines())
    imports = [] if has_imports else ["HJBrigade"]
    namespace = None if has_imports else "HJBrigade"

    patched_src, line_map = _inject_trace_state(src)
    res = await verifier.check(patched_src, imports=imports, namespace=namespace)
    header_offset = 0
    if not has_imports:
        # `build_check_source` prepends `import HJBrigade\nset_option ...\nopen HJBrigade\n\n`
        full = verifier.build_check_source(patched_src, imports=imports, namespace=namespace)
        # Find where patched_src starts
        prefix = full[: full.find(patched_src)]
        header_offset = prefix.count("\n")

    located_goals = _parse_located_goals(res.raw_output)
    items: list[BlueprintItem] = []

    for b in blocks:
        item = BlueprintItem(
            name=b["name"],
            kind=b["kind"],
            start_line=b["start_line"],
            end_line=b["end_line"],
            signature=b["signature"],
            has_sorry=b["has_sorry"],
        )
        if b["has_sorry"]:
            matched_goals: list[str] = []
            for raw_ln, gtxt in located_goals:
                adj_ln = raw_ln - header_offset
                orig_ln = line_map.get(adj_ln, adj_ln)
                if b["start_line"] <= orig_ln <= b["end_line"]:
                    matched_goals.append(gtxt)
            item.goals = matched_goals
            query = f"{b['name']} {b['signature']} " + " ".join(matched_goals)
            item.premise_hints = index.format_hints(query, limit=6)
        else:
            lint = lint_proof(b["text"])
            if lint:
                item.axiom_ok = False
                item.note = "; ".join(lint)
            else:
                prefix_src = "\n".join(src.splitlines()[: b["end_line"]])
                if _SORRY_TOKEN_RE.search(strip_lean_comments(prefix_src)):
                    item.axiom_ok = None
                    item.note = "preceded by open `sorry` theorems (audit deferred until dependencies close)"
                else:
                    aud = await verifier.axiom_audit(
                        prefix_src,
                        b["name"],
                        imports=imports,
                        namespace=namespace,
                    )
                    item.axiom_ok = aud.ok
                    item.axioms = aud.axioms
                    item.note = aud.note
        items.append(item)

    return {
        "file": str(lean_file),
        "compile_ok": res.ok,
        "errors": res.errors,
        "total_theorems": len(items),
        "open_count": sum(1 for i in items if i.has_sorry),
        "completed_count": sum(1 for i in items if not i.has_sorry),
        "items": [
            {
                "name": i.name,
                "kind": i.kind,
                "lines": [i.start_line, i.end_line],
                "signature": i.signature,
                "has_sorry": i.has_sorry,
                "goals": i.goals,
                "premise_hints": i.premise_hints,
                "axiom_ok": i.axiom_ok,
                "axioms": i.axioms,
                "note": i.note,
            }
            for i in items
        ],
    }
