"""Incremental Lean 4 module builder (`lake build` with direct `lean.exe` topological fallback)."""

from __future__ import annotations

import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from brigade.lean_verifier import find_elan_toolchain_bin  # noqa: E402

_IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)\b", re.MULTILINE)


def _discover_modules(proj: Path) -> list[str]:
    mods: list[str] = []
    root_file = proj / "HJBrigade.lean"
    lib_dir = proj / "HJBrigade"
    for p in sorted(lib_dir.rglob("*.lean")):
        rel = p.relative_to(proj).with_suffix("")
        mods.append(".".join(rel.parts))
    if root_file.exists():
        mods.append("HJBrigade")
    return mods


def _mod_lean_path(proj: Path, mod: str) -> Path:
    return proj.joinpath(*mod.split(".")).with_suffix(".lean")


def _mod_olean_path(proj: Path, mod: str) -> Path:
    return proj / ".lake" / "build" / "lib" / "lean" / Path(*mod.split(".")).with_suffix(".olean")


def _topo_sort(proj: Path, targets: list[str]) -> list[str]:
    all_mods = set(_discover_modules(proj))
    deps: dict[str, list[str]] = {}
    for m in all_mods:
        src = _mod_lean_path(proj, m).read_text(encoding="utf-8", errors="replace")
        deps[m] = [imp for imp in _IMPORT_RE.findall(src) if imp in all_mods]

    order: list[str] = []
    state: dict[str, int] = {}

    def visit(m: str) -> None:
        st = state.get(m, 0)
        if st == 2:
            return
        if st == 1:
            raise RuntimeError(f"Cyclic import involving {m}")
        state[m] = 1
        for d in deps.get(m, []):
            visit(d)
        state[m] = 2
        order.append(m)

    for t in targets:
        if t in all_mods:
            visit(t)
    return order


def build_with_lean(proj: Path, targets: list[str] | None = None, force: bool = False) -> int:
    bin_dir = find_elan_toolchain_bin()
    if bin_dir is None:
        print("Error: could not locate Lean toolchain binaries.", file=sys.stderr)
        return 1
    exe_ext = ".exe" if os.name == "nt" else ""
    lake_bin = bin_dir / f"lake{exe_ext}"
    lean_bin = bin_dir / f"lean{exe_ext}"

    if lake_bin.exists():
        try:
            cmd = [str(lake_bin), "--dir", str(proj), "build", *(targets or [])]
            proc = subprocess.run(cmd, cwd=str(proj), stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            if proc.returncode == 0:
                if proc.stdout:
                    print(proc.stdout, end="")
                return 0
            # Fall back cleanly when Windows App Control / elan blocks lake.exe
            err_msg = (proc.stderr or "") + (proc.stdout or "")
            if "4551" not in err_msg and "failed: 'lake.exe'" not in err_msg:
                if proc.stdout:
                    print(proc.stdout, end="")
                if proc.stderr:
                    print(proc.stderr, end="", file=sys.stderr)
        except OSError:
            pass

    all_targets = targets or _discover_modules(proj)
    order = _topo_sort(proj, all_targets)
    env = os.environ.copy()
    env["LEAN_PATH"] = str(proj / ".lake" / "build" / "lib" / "lean")

    rebuilt_deps: set[str] = set()
    built = 0
    for mod in order:
        src = _mod_lean_path(proj, mod)
        out = _mod_olean_path(proj, mod)
        out.parent.mkdir(parents=True, exist_ok=True)
        src_text = src.read_text(encoding="utf-8", errors="replace")
        imports = _IMPORT_RE.findall(src_text)
        dep_dirty = any(imp in rebuilt_deps for imp in imports)
        needs_build = (
            force
            or dep_dirty
            or not out.exists()
            or src.stat().st_mtime > out.stat().st_mtime
            or any(
                _mod_olean_path(proj, imp).exists()
                and _mod_olean_path(proj, imp).stat().st_mtime > out.stat().st_mtime
                for imp in imports
            )
        )
        if not needs_build:
            continue
        proc = subprocess.run(
            [str(lean_bin), str(src), "-o", str(out), "-R", str(proj)],
            cwd=str(proj),
            env=env,
        )
        if proc.returncode != 0:
            return proc.returncode
        rebuilt_deps.add(mod)
        built += 1
        print(f"Built {mod}")
    if built == 0:
        print("All targets up to date.")
    else:
        print(f"Build completed successfully ({built} module(s) built).")
    return 0


def main() -> int:
    args = sys.argv[1:]
    force = "--force" in args
    targets = [a for a in args if not a.startswith("-")]
    return build_with_lean(ROOT, targets=targets or None, force=force)


if __name__ == "__main__":
    raise SystemExit(main())
