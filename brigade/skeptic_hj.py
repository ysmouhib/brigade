"""Exact combinatorial Hales-Jewett solver and Lean 4 certificate compiler."""

from __future__ import annotations

from dataclasses import dataclass
import random
import time
from typing import Any

from .models import HJSearchResult


def decode_word(idx: int, d: int, k: int) -> tuple[int, ...]:
    coords: list[int] = []
    cur = idx
    for _ in range(d):
        coords.append(cur % k)
        cur //= k
    return tuple(coords)


def encode_word(coords: tuple[int, ...] | list[int], k: int) -> int:
    val = 0
    mul = 1
    for c in coords:
        val += c * mul
        mul *= k
    return val


def generate_lines(d: int, k: int) -> list[tuple[tuple[int | None, ...], tuple[int, ...]]]:
    """Generate all `(k+1)^d - k^d` combinatorial lines as `(mask, word_indices)`."""
    if d <= 0:
        return []
    lines: list[tuple[tuple[int | None, ...], tuple[int, ...]]] = []
    choices: list[int | None] = [None, *range(k)]

    def rec(pos: int, cur_mask: list[int | None], has_wild: bool) -> None:
        if pos == d:
            if not has_wild:
                return
            mask = tuple(cur_mask)
            pts = tuple(
                encode_word([t if x is None else x for x in mask], k)
                for t in range(k)
            )
            lines.append((mask, pts))
            return
        for ch in choices:
            cur_mask.append(ch)
            rec(pos + 1, cur_mask, has_wild or (ch is None))
            cur_mask.pop()

    rec(0, [], False)
    return lines


@dataclass
class CertWitness:
    mask: tuple[int | None, ...]
    color: int


@dataclass
class CertSplit:
    pt_idx: int
    branches: list[Any]


def _walksat_probe(
    num_words: int,
    lines: list[tuple[tuple[int | None, ...], tuple[int, ...]]],
    r: int,
    steps: int = 1500,
    seed: int = 42,
) -> list[int] | None:
    if not lines:
        return [0] * num_words
    rng = random.Random(seed)
    pt_lines: list[list[int]] = [[] for _ in range(num_words)]
    for li, (_, pts) in enumerate(lines):
        for p in pts:
            pt_lines[p].append(li)

    for _restart in range(3):
        col = [rng.randrange(r) for _ in range(num_words)]
        bad: set[int] = set()
        for li, (_, pts) in enumerate(lines):
            c0 = col[pts[0]]
            if all(col[p] == c0 for p in pts[1:]):
                bad.add(li)
        if not bad:
            return col
        for _ in range(steps):
            if not bad:
                return col
            li = rng.choice(tuple(bad))
            pts = lines[li][1]
            best_move: tuple[int, int] | None = None
            best_delta = 10**9
            for p in pts:
                old_c = col[p]
                for nc in range(r):
                    if nc == old_c:
                        continue
                    delta = 0
                    for ali in pt_lines[p]:
                        apts = lines[ali][1]
                        was_mono = ali in bad
                        col[p] = nc
                        c0 = col[apts[0]]
                        now_mono = all(col[q] == c0 for q in apts[1:])
                        col[p] = old_c
                        if now_mono and not was_mono:
                            delta += 1
                        elif was_mono and not now_mono:
                            delta -= 1
                    if delta < best_delta or (delta == best_delta and rng.random() < 0.35):
                        best_delta = delta
                        best_move = (p, nc)
            if best_move is None:
                p = rng.choice(pts)
                nc = (col[p] + rng.randrange(1, r)) % r
            else:
                p, nc = best_move
            col[p] = nc
            for ali in pt_lines[p]:
                apts = lines[ali][1]
                c0 = col[apts[0]]
                if all(col[q] == c0 for q in apts[1:]):
                    bad.add(ali)
                else:
                    bad.discard(ali)
        if not bad:
            return col
    return None


def solve_hj(
    d: int,
    k: int,
    r: int,
    max_nodes: int = 500_000,
    time_limit_s: float = 20.0,
) -> HJSearchResult:
    """Solve whether `HJUpper d k r` holds, returning either a line-free witness or CertTree."""
    t0 = time.perf_counter()
    num_words = k**d if k > 0 else (1 if d == 0 else 0)
    lines = generate_lines(d, k)

    if d == 0 or k == 0 or r <= 0:
        witness = [0] * num_words if r > 0 and num_words > 0 else []
        return HJSearchResult(
            d=d, k=k, r=r, status="SAT_LINE_FREE" if r > 0 else "UNSAT_MONO_FORCED",
            num_words=num_words, num_lines=len(lines), nodes_explored=1,
            elapsed_s=time.perf_counter() - t0, witness_coloring=witness,
        )

    if k == 1:
        tree = CertSplit(pt_idx=0, branches=[CertWitness(mask=tuple([None] * d), color=c) for c in range(r)])
        return HJSearchResult(
            d=d, k=k, r=r, status="UNSAT_MONO_FORCED",
            num_words=num_words, num_lines=len(lines), nodes_explored=1,
            elapsed_s=time.perf_counter() - t0, cert_tree=tree,
        )

    if r == 1:
        # Every line is monochromatic; branch along all `k` words of `[None]*d`.
        mask = tuple([None] * d)
        pts = [encode_word([t] * d, k) for t in range(k)]
        node: Any = CertWitness(mask=mask, color=0)
        for p in reversed(pts):
            node = CertSplit(pt_idx=p, branches=[node])
        return HJSearchResult(
            d=d, k=k, r=r, status="UNSAT_MONO_FORCED",
            num_words=num_words, num_lines=len(lines), nodes_explored=1,
            elapsed_s=time.perf_counter() - t0, cert_tree=node,
        )

    # Quick WalkSAT probe to catch obvious lower-bound witnesses before full DPLL
    if k >= 2 and r >= 2 and d >= 1:
        sat_guess = _walksat_probe(num_words, lines, r, steps=800)
        if sat_guess is not None:
            return HJSearchResult(
                d=d, k=k, r=r, status="SAT_LINE_FREE",
                num_words=num_words, num_lines=len(lines), nodes_explored=1,
                elapsed_s=time.perf_counter() - t0, witness_coloring=sat_guess,
            )

    pt_lines: list[list[int]] = [[] for _ in range(num_words)]
    for li, (_, pts) in enumerate(lines):
        for p in pts:
            pt_lines[p].append(li)

    # Symmetry breaking: for r >= 2, fix the highest-degree vertex (center word) to color 0.
    root_sym_idx: int | None = None
    assigned: list[int] = [-1] * num_words
    if r >= 2:
        root_sym_idx = max(range(num_words), key=lambda p: len(pt_lines[p]))
        assigned[root_sym_idx] = 0

    nodes_explored = 0
    aborted = False

    def check_point_lines(p: int) -> CertWitness | None:
        """Check if assigning `p` made any incident line monochromatic."""
        col = assigned[p]
        for li in pt_lines[p]:
            mask, pts = lines[li]
            if all(assigned[q] == col for q in pts):
                return CertWitness(mask=mask, color=col)
        return None

    def collect_used_pts(witness: CertWitness) -> set[int]:
        mask = witness.mask
        return {
            encode_word([t if x is None else x for x in mask], k)
            for t in range(k)
        }

    def find_unit_forcing() -> tuple[int, int, int] | None:
        """Return `(unassigned_pt, forbidden_color, line_idx)` if any line has `k-1` same-color pts."""
        for li, (_, pts) in enumerate(lines):
            unassigned_pt = -1
            unassigned_cnt = 0
            target_col = -1
            mixed = False
            for p in pts:
                cp = assigned[p]
                if cp == -1:
                    unassigned_pt = p
                    unassigned_cnt += 1
                    if unassigned_cnt > 1:
                        break
                else:
                    if target_col == -1:
                        target_col = cp
                    elif target_col != cp:
                        mixed = True
                        break
            if not mixed and unassigned_cnt == 1 and target_col != -1:
                return (unassigned_pt, target_col, li)
        return None

    def pick_branch_var() -> int:
        # Score unassigned variables by nearly-monochromatic incident lines + total degree
        best_p = -1
        best_score = -1
        for p in range(num_words):
            if assigned[p] != -1:
                continue
            score = 0
            for li in pt_lines[p]:
                pts = lines[li][1]
                cols = {assigned[q] for q in pts if assigned[q] != -1}
                if len(cols) <= 1:
                    filled = sum(1 for q in pts if assigned[q] != -1)
                    score += 1 + filled * filled * 4
            if score > best_score:
                best_score = score
                best_p = p
        if best_p != -1:
            return best_p
        return next(p for p in range(num_words) if assigned[p] == -1)

    def dpll() -> tuple[bool, Any, set[int]]:
        """Returns `(is_sat, witness_or_cert, used_pts_if_unsat)`."""
        nonlocal nodes_explored, aborted
        nodes_explored += 1
        if nodes_explored > max_nodes or (nodes_explored & 255 == 0 and time.perf_counter() - t0 > time_limit_s):
            aborted = True
            return (True, None, set())

        # Check if any unassigned point exists
        if all(c != -1 for c in assigned):
            return (True, list(assigned), set())

        # Unit-forced branching first
        unit = find_unit_forcing()
        if unit is not None:
            p, bad_col, li = unit
            branch_pt = p
            order = [bad_col, *[c for c in range(r) if c != bad_col]]
        else:
            branch_pt = pick_branch_var()
            order = list(range(r))

        sub_trees: list[Any] = [None] * r
        used_union: set[int] = set()

        for col in order:
            assigned[branch_pt] = col
            hit = check_point_lines(branch_pt)
            if hit is not None:
                used = collect_used_pts(hit)
                sub_trees[col] = hit
                assigned[branch_pt] = -1
                if branch_pt not in used:
                    return (False, hit, used)
                used_union |= used
                continue

            sat, sub, sub_used = dpll()
            assigned[branch_pt] = -1
            if aborted:
                return (True, None, set())
            if sat:
                return (True, sub, set())
            if branch_pt not in sub_used:
                # Backjumping: this branch didn't even need branch_pt!
                return (False, sub, sub_used)
            sub_trees[col] = sub
            used_union |= sub_used

        used_union.discard(branch_pt)
        return (False, CertSplit(pt_idx=branch_pt, branches=sub_trees), used_union)

    if root_sym_idx is not None:
        hit0 = check_point_lines(root_sym_idx)
        if hit0 is not None:
            return HJSearchResult(
                d=d, k=k, r=r, status="UNSAT_MONO_FORCED",
                num_words=num_words, num_lines=len(lines), nodes_explored=1,
                elapsed_s=time.perf_counter() - t0, cert_tree=hit0, root_sym_idx=root_sym_idx,
            )

    is_sat, payload, _ = dpll()
    elapsed = time.perf_counter() - t0
    if aborted:
        return HJSearchResult(
            d=d, k=k, r=r, status="UNKNOWN",
            num_words=num_words, num_lines=len(lines), nodes_explored=nodes_explored,
            elapsed_s=elapsed,
        )
    if is_sat:
        return HJSearchResult(
            d=d, k=k, r=r, status="SAT_LINE_FREE",
            num_words=num_words, num_lines=len(lines), nodes_explored=nodes_explored,
            elapsed_s=elapsed, witness_coloring=payload,
        )
    return HJSearchResult(
        d=d, k=k, r=r, status="UNSAT_MONO_FORCED",
        num_words=num_words, num_lines=len(lines), nodes_explored=nodes_explored,
        elapsed_s=elapsed, cert_tree=payload, root_sym_idx=root_sym_idx,
    )


def _format_cert_tree(node: Any, indent: int = 2) -> str:
    pad = " " * indent
    if isinstance(node, CertWitness):
        mask_items = ", ".join("none" if x is None else f"some {x}" for x in node.mask)
        return f"{pad}.witness [{mask_items}] {node.color}"
    assert isinstance(node, CertSplit)
    inner = ",\n".join(_format_cert_tree(b, indent + 4) for b in node.branches)
    return f"{pad}.split {node.pt_idx} [\n{inner}\n{pad}]"


def emit_upper_bound_lean(res: HJSearchResult, theorem_name: str | None = None) -> str:
    """Emit a self-contained kernel-checked Lean 4 theorem proving `HJUpper d k r`."""
    if res.status != "UNSAT_MONO_FORCED" or res.cert_tree is None:
        raise ValueError("Can only emit upper-bound Lean certificate for UNSAT result")
    name = theorem_name or f"hj_{res.k}_{res.r}_le_{res.d}"
    cert_name = f"{name}_cert"
    tree_lit = _format_cert_tree(res.cert_tree, indent=2)
    if res.r == 2 and res.root_sym_idx is not None:
        proof_line = (
            f"  exact checkCertSym2_sound {res.d} {res.k} (by decide) {res.root_sym_idx} {cert_name} (by decide)"
        )
    elif res.root_sym_idx is not None:
        proof_line = (
            f"  exact checkCertSym_sound {res.d} {res.k} {res.r} (by decide) (by decide) "
            f"{res.root_sym_idx} {cert_name} (by decide)"
        )
    else:
        proof_line = (
            f"  exact checkCert_sound {res.d} {res.k} {res.r} (by decide) {cert_name} (by decide)"
        )
    return (
        f"private def {cert_name} : CertTree {res.r} :=\n"
        f"{tree_lit}\n\n"
        f"theorem {name} : HJUpper {res.d} {res.k} {res.r} := by\n"
        f"{proof_line}\n"
    )


def solve_vdw(N: int, k: int, r: int, steps: int = 3000) -> dict[str, Any]:
    """Search for an AP-free `r`-coloring of `{0, ..., N-1}` avoiding `k`-APs."""
    t0 = time.perf_counter()
    if k <= 1 or N < k or r <= 0:
        status = "UNSAT_MONO_FORCED" if (k <= 1 and N >= 1 and r >= 1) or r <= 0 else "SAT_AP_FREE"
        return {"N": N, "k": k, "r": r, "status": status, "coloring": [0] * N, "elapsed_s": time.perf_counter() - t0}

    aps: list[tuple[int, ...]] = []
    for a in range(N):
        max_step = (N - 1 - a) // (k - 1)
        for step in range(1, max_step + 1):
            aps.append(tuple(a + t * step for t in range(k)))

    if not aps:
        return {"N": N, "k": k, "r": r, "status": "SAT_AP_FREE", "coloring": [0] * N, "elapsed_s": time.perf_counter() - t0}

    if r == 1:
        return {"N": N, "k": k, "r": r, "status": "UNSAT_MONO_FORCED", "coloring": None, "elapsed_s": time.perf_counter() - t0}

    # WalkSAT probe first
    fake_lines = [((), ap) for ap in aps]
    guess = _walksat_probe(N, fake_lines, r, steps=steps)
    if guess is not None:
        return {"N": N, "k": k, "r": r, "status": "SAT_AP_FREE", "coloring": guess, "elapsed_s": time.perf_counter() - t0}

    # Exact DPLL check for small N
    if N <= 32:
        assigned = [-1] * N
        assigned[0] = 0
        pt_aps: list[list[int]] = [[] for _ in range(N)]
        for ai, ap in enumerate(aps):
            for p in ap:
                pt_aps[p].append(ai)

        def is_mono(p: int) -> bool:
            cp = assigned[p]
            return any(all(assigned[q] == cp for q in aps[ai]) for ai in pt_aps[p])

        def backtrack() -> list[int] | None:
            for p in range(N):
                if assigned[p] == -1:
                    for col in range(r):
                        assigned[p] = col
                        if not is_mono(p):
                            res = backtrack()
                            if res is not None:
                                return res
                        assigned[p] = -1
                    return None
            return list(assigned)

        sol = backtrack()
        if sol is not None:
            return {"N": N, "k": k, "r": r, "status": "SAT_AP_FREE", "coloring": sol, "elapsed_s": time.perf_counter() - t0}
        return {"N": N, "k": k, "r": r, "status": "UNSAT_MONO_FORCED", "coloring": None, "elapsed_s": time.perf_counter() - t0}

    return {"N": N, "k": k, "r": r, "status": "UNKNOWN", "coloring": None, "elapsed_s": time.perf_counter() - t0}


def emit_vdw_lower_lean(N: int, k: int, r: int, coloring: list[int], theorem_name: str | None = None) -> str:
    """Emit a Lean 4 kernel-checked witness proving `¬ HasMonoAP N k r`."""
    name = theorem_name or f"vdw_{k}_{r}_gt_{N}"
    tbl = ", ".join(str(c) for c in coloring)
    wit = f"{name}_witness"
    return (
        f"private def {wit} (i : Fin {N}) : Fin {r} :=\n"
        f"  ⟨([{tbl}].getD i.val 0) % {r}, Nat.mod_lt _ (by decide)⟩\n\n"
        f"theorem {name} : ¬ HasMonoAP {N} {k} {r} := by\n"
        f"  intro h\n"
        f"  have hfor : HasMonoAPFor {N} {k} {r} {wit} := (hasMonoAP_iff_for {N} {k} {r}).mp h {wit}\n"
        f"  revert hfor\n"
        f"  decide\n"
    )


def emit_lower_bound_lean(res: HJSearchResult, theorem_name: str | None = None) -> str:
    """Emit a self-contained kernel-checked Lean 4 witness proving `¬ HJUpper d k r`."""
    if res.status != "SAT_LINE_FREE" or res.witness_coloring is None:
        raise ValueError("Can only emit lower-bound witness for SAT_LINE_FREE result")
    name = theorem_name or f"hj_{res.k}_{res.r}_gt_{res.d}"
    d, k, r = res.d, res.k, res.r
    coloring = res.witness_coloring
    col_name = f"{name}_coloring"

    # Encode word index in Lean matching Python's base-k encoding: sum_{i} w(i) * k^i
    lines_idx = ", ".join(str(c) for c in coloring)
    return (
        f"private def {col_name}_tbl : List Nat := [{lines_idx}]\n\n"
        f"private def {col_name}_idx (w : Word {d} {k}) : Nat :=\n"
        f"  (List.range {d}).foldl (fun acc i =>\n"
        f"    if hi : i < {d} then acc + (w ⟨i, hi⟩).val * {k} ^ i else acc) 0\n\n"
        f"private def {col_name} (w : Word {d} {k}) : Fin {r} :=\n"
        f"  ⟨({col_name}_tbl.getD ({col_name}_idx w) 0) % {r}, Nat.mod_lt _ (by decide)⟩\n\n"
        f"theorem {name} : ¬ HJUpper {d} {k} {r} := by\n"
        f"  intro h\n"
        f"  have hmono : HasMonoLine {d} {k} {r} {col_name} := h {col_name}\n"
        f"  revert hmono\n"
        f"  decide\n"
    )
