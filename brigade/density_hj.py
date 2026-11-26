"""Density Hales-Jewett & Moser solver (exact DFS, Fujimura simplex B&B, local search) & Lean compiler."""

from __future__ import annotations

from dataclasses import dataclass
import itertools
import math
import random
import time

from .skeptic_hj import generate_lines


@dataclass
class DHJSearchResult:
    d: int
    k: int
    num_words: int
    size: int
    optimal: bool
    indicator: list[int]
    elapsed_s: float
    fujimura_triples: list[tuple[int, int, int]] | None = None


def generate_geom_lines(d: int) -> list[tuple[tuple[int | str, ...], tuple[int, ...]]]:
    """Generate all unique geometric lines in `[3]^d` (where active coords move by `+1` or `-1`)."""
    words = list(itertools.product(range(3), repeat=d))
    idx = {tuple(reversed(w)): sum(w[i] * (3**i) for i in range(d)) for w in words}
    # Ensure canonical little-endian index: w[0] + 3*w[1] + ... matching Lean foldl
    idx = {w: sum(w[i] * (3**i) for i in range(d)) for w in words}
    seen: set[tuple[int, ...]] = set()
    lines: list[tuple[tuple[int | str, ...], tuple[int, ...]]] = []
    for mask in itertools.product((0, 1, 2, "+", "-"), repeat=d):
        if "+" not in mask and "-" not in mask:
            continue
        pts = tuple(
            idx[tuple(t if m == "+" else (2 - t if m == "-" else m) for m in mask)]
            for t in range(3)
        )
        canon = min(pts, pts[::-1])
        if canon not in seen:
            seen.add(canon)
            lines.append((mask, canon))
    return lines


def _check_line_free(indicator: list[int], lines: list[tuple[tuple[int | str | None, ...], tuple[int, ...]]]) -> bool:
    for _, pts in lines:
        if all(indicator[p] == 1 for p in pts):
            return False
    return True


def _solve_dhj_exact(num_words: int, k: int, lines: list[tuple[tuple[int | str | None, ...], tuple[int, ...]]]) -> list[int]:
    pt_lines: list[list[int]] = [[] for _ in range(num_words)]
    for li, (_, pts) in enumerate(lines):
        for p in pts:
            pt_lines[p].append(li)

    order = sorted(range(num_words), key=lambda p: len(pt_lines[p]))
    cur = [0] * num_words
    best = [0] * num_words
    best_size = 0
    line_cnt = [0] * len(lines)

    def dfs(pos: int, cur_size: int) -> None:
        nonlocal best_size, best
        if cur_size + (num_words - pos) <= best_size:
            return
        if pos == num_words:
            best_size = cur_size
            best = list(cur)
            return
        p = order[pos]
        if all(line_cnt[li] < k - 1 for li in pt_lines[p]):
            cur[p] = 1
            for li in pt_lines[p]:
                line_cnt[li] += 1
            dfs(pos + 1, cur_size + 1)
            for li in pt_lines[p]:
                line_cnt[li] -= 1
            cur[p] = 0
        dfs(pos + 1, cur_size)

    dfs(0, 0)
    return best


def _local_search_dhj(
    d: int,
    k: int,
    num_words: int,
    lines: list[tuple[tuple[int | str | None, ...], tuple[int, ...]]],
    restarts: int = 30,
    steps: int = 1200,
    seed: int = 42,
    initial: list[int] | None = None,
) -> list[int]:
    rng = random.Random(seed)
    pt_lines: list[list[int]] = [[] for _ in range(num_words)]
    for li, (_, pts) in enumerate(lines):
        for p in pts:
            pt_lines[p].append(li)

    best_ind: list[int] = list(initial) if initial is not None else []
    best_size = sum(best_ind) if best_ind else -1

    for restart in range(restarts):
        if restart == 0 and initial is not None:
            ind = list(initial)
            cur_size = sum(ind)
            line_cnt = [sum(ind[p] for p in pts) for _, pts in lines]
        else:
            ind = [0] * num_words
            line_cnt = [0] * len(lines)
            cur_size = 0
            perm = list(range(num_words))
            rng.shuffle(perm)
            if restart % 2 == 0 and k >= 3:
                def balance_score(idx: int) -> tuple[int, float]:
                    coords = []
                    c = idx
                    for _ in range(d):
                        coords.append(c % k)
                        c //= k
                    counts = [coords.count(t) for t in range(k)]
                    return (max(counts) - min(counts), rng.random())

                perm.sort(key=balance_score)

            for p in perm:
                if all(line_cnt[li] < k - 1 for li in pt_lines[p]):
                    ind[p] = 1
                    cur_size += 1
                    for li in pt_lines[p]:
                        line_cnt[li] += 1

        for _ in range(steps):
            chosen = [p for p in range(num_words) if ind[p] == 1]
            if not chosen:
                break
            snap_ind = list(ind)
            snap_cnt = list(line_cnt)
            snap_size = cur_size

            drop_k = 1 if rng.random() < 0.55 else min(2, len(chosen))
            for dp in rng.sample(chosen, drop_k):
                ind[dp] = 0
                cur_size -= 1
                for li in pt_lines[dp]:
                    line_cnt[li] -= 1

            cands = [p for p in range(num_words) if ind[p] == 0]
            rng.shuffle(cands)
            for p in cands:
                if all(line_cnt[li] < k - 1 for li in pt_lines[p]):
                    ind[p] = 1
                    cur_size += 1
                    for li in pt_lines[p]:
                        line_cnt[li] += 1

            if cur_size < snap_size and rng.random() < 0.8:
                ind = snap_ind
                line_cnt = snap_cnt
                cur_size = snap_size

            if cur_size > best_size:
                best_size = cur_size
                best_ind = list(ind)

        if cur_size > best_size:
            best_size = cur_size
            best_ind = list(ind)

    assert _check_line_free(best_ind, lines)
    return best_ind


def _triples_to_indicator(d: int, triples: list[tuple[int, int, int]]) -> list[int]:
    tset = set(triples)
    num_words = 3**d
    ind = [0] * num_words
    for idx in range(num_words):
        x = idx
        cnt = [0, 0, 0]
        for _ in range(d):
            cnt[x % 3] += 1
            x //= 3
        if (cnt[0], cnt[1], cnt[2]) in tset:
            ind[idx] = 1
    return ind


def _solve_simplex_symmetric(d: int, *, geometric: bool) -> tuple[int, list[tuple[int, int, int]]]:
    """Exact branch-and-bound for maximum `S_d`-invariant line-free subset of `[3]^d`."""
    fact_d = math.factorial(d)
    pts = sorted(
        [(a, b, d - a - b) for a in range(d + 1) for b in range(d + 1 - a)],
        key=lambda p: -fact_d // (math.factorial(p[0]) * math.factorial(p[1]) * math.factorial(p[2])),
    )
    wts = [fact_d // (math.factorial(a) * math.factorial(b) * math.factorial(c)) for a, b, c in pts]
    pidx = {p: i for i, p in enumerate(pts)}

    forb_sets: set[tuple[int, ...]] = set()
    if geometric:
        for a in range(d + 1):
            for b in range(d + 1 - a):
                for c in range(d + 1 - a - b):
                    rem = d - (a + b + c)
                    if rem < 1:
                        continue
                    for p in range(rem + 1):
                        q = rem - p
                        forb_sets.add(tuple(sorted({
                            pidx[(a + p, b, c + q)],
                            pidx[(a, b + p + q, c)],
                            pidx[(a + q, b, c + p)],
                        })))
    else:
        for a in range(d + 1):
            for b in range(d + 1 - a):
                for c in range(d + 1 - a - b):
                    r = d - (a + b + c)
                    if r < 1:
                        continue
                    forb_sets.add(tuple(sorted({
                        pidx[(a + r, b, c)],
                        pidx[(a, b + r, c)],
                        pidx[(a, b, c + r)],
                    })))

    n = len(pts)
    pt_triples: list[list[tuple[int, ...]]] = [[] for _ in range(n)]
    for fs in forb_sets:
        for i in fs:
            if i == max(fs):
                pt_triples[i].append(tuple(u for u in fs if u != i))

    suffix = [0] * (n + 1)
    for i in range(n - 1, -1, -1):
        suffix[i] = suffix[i + 1] + wts[i]

    best_size = 0
    best_mask: list[int] = []
    cur = [0] * n

    def dfs(i: int, sz: int) -> None:
        nonlocal best_size, best_mask
        if sz + suffix[i] <= best_size:
            return
        if i == n:
            best_size = sz
            best_mask = list(cur)
            return
        if all(any(cur[u] == 0 for u in req) for req in pt_triples[i]):
            cur[i] = 1
            dfs(i + 1, sz + wts[i])
            cur[i] = 0
        dfs(i + 1, sz)

    dfs(0, 0)
    chosen = sorted(pts[i] for i in range(n) if best_mask[i])
    return best_size, chosen


def solve_fujimura(d: int) -> tuple[int, list[tuple[int, int, int]]]:
    """Find optimal `S_d`-invariant (Fujimura simplex-free) combinatorial line-free subset of `[3]^d`."""
    return _solve_simplex_symmetric(d, geometric=False)


def solve_dhj(d: int, k: int, restarts: int = 30, steps: int = 1200) -> DHJSearchResult:
    """Find a maximum (exact for small `k^d <= 27`, heuristic + Fujimura otherwise) line-free subset of `[k]^d`."""
    t0 = time.perf_counter()
    num_words = k**d if k > 0 else (1 if d == 0 else 0)
    lines = generate_lines(d, k)
    if d == 0 or k == 0:
        ind = [1] * num_words
        return DHJSearchResult(
            d=d, k=k, num_words=num_words, size=sum(ind),
            optimal=True, indicator=ind, elapsed_s=time.perf_counter() - t0,
        )
    if num_words <= 27:
        ind = _solve_dhj_exact(num_words, k, lines)
        return DHJSearchResult(
            d=d, k=k, num_words=num_words, size=sum(ind),
            optimal=True, indicator=ind, elapsed_s=time.perf_counter() - t0,
        )

    fuj_triples: list[tuple[int, int, int]] | None = None
    fuj_ind: list[int] | None = None
    if k == 3 and d >= 4:
        f_sz, f_tr = solve_fujimura(d)
        fuj_triples = f_tr
        fuj_ind = _triples_to_indicator(d, f_tr)
        assert _check_line_free(fuj_ind, lines)

    if k == 3 and d >= 5 and fuj_ind is not None:
        return DHJSearchResult(
            d=d, k=k, num_words=num_words, size=sum(fuj_ind),
            optimal=False, indicator=fuj_ind, elapsed_s=time.perf_counter() - t0,
            fujimura_triples=fuj_triples,
        )

    ind = _local_search_dhj(d, k, num_words, lines, restarts=restarts, steps=steps, initial=fuj_ind)
    if fuj_ind is not None and sum(fuj_ind) >= sum(ind):
        ind = fuj_ind
    else:
        fuj_triples = None
    return DHJSearchResult(
        d=d, k=k, num_words=num_words, size=sum(ind),
        optimal=False, indicator=ind, elapsed_s=time.perf_counter() - t0,
        fujimura_triples=fuj_triples,
    )


def solve_moser(d: int, restarts: int = 30, steps: int = 1200) -> DHJSearchResult:
    """Find a maximum (exact for `d <= 3`, `S_d`-invariant + local search otherwise) geometric-line-free set in `[3]^d`."""
    t0 = time.perf_counter()
    num_words = 3**d
    if d == 0:
        return DHJSearchResult(
            d=0, k=3, num_words=1, size=1, optimal=True, indicator=[1], elapsed_s=time.perf_counter() - t0
        )
    lines = generate_geom_lines(d)
    if d <= 3:
        ind = _solve_dhj_exact(num_words, 3, lines)
        return DHJSearchResult(
            d=d, k=3, num_words=num_words, size=sum(ind),
            optimal=True, indicator=ind, elapsed_s=time.perf_counter() - t0,
        )
    f_sz, f_tr = _solve_simplex_symmetric(d, geometric=True)
    f_ind = _triples_to_indicator(d, f_tr)
    assert _check_line_free(f_ind, lines)
    if d >= 5:
        return DHJSearchResult(
            d=d, k=3, num_words=num_words, size=f_sz,
            optimal=False, indicator=f_ind, elapsed_s=time.perf_counter() - t0,
            fujimura_triples=f_tr,
        )
    ind = _local_search_dhj(d, 3, num_words, lines, restarts=restarts, steps=steps, initial=f_ind)
    if f_sz >= sum(ind):
        return DHJSearchResult(
            d=d, k=3, num_words=num_words, size=f_sz,
            optimal=False, indicator=f_ind, elapsed_s=time.perf_counter() - t0,
            fujimura_triples=f_tr,
        )
    return DHJSearchResult(
        d=d, k=3, num_words=num_words, size=sum(ind),
        optimal=False, indicator=ind, elapsed_s=time.perf_counter() - t0,
    )


def emit_fujimura_lower_lean(
    d: int,
    triples: list[tuple[int, int, int]],
    size: int,
    theorem_name: str | None = None,
    *,
    geometric: bool = False,
) -> str:
    """Emit a compact `fujimura_lower_bound` or `moser_fujimura_lower_bound` theorem."""
    prefix = "moser" if geometric else "dhj"
    name = theorem_name or f"{prefix}_{d}_3_ge_{size}"
    tr_name = f"{name}_triples"
    triples_lit = ", ".join(f"({a}, {b}, {c})" for a, b, c in triples)
    pred = "IsGeomLineFree" if geometric else "IsLineFree"
    lemma = "moser_fujimura_lower_bound" if geometric else "fujimura_lower_bound"
    return (
        f"private def {tr_name} : List (Nat × Nat × Nat) :=\n"
        f"  [{triples_lit}]\n\n"
        f"theorem {name} : ∃ A : Word {d} 3 → Bool, {pred} A ∧ wordCard A = {size} :=\n"
        f"  {lemma} {d} {size} {tr_name} (by decide) (by decide)\n"
    )


def _emit_flat_table_lower_lean(
    res: DHJSearchResult,
    theorem_name: str,
    *,
    geometric: bool = False,
) -> str:
    d, k, sz = res.d, res.k, res.size
    tbl_name = f"{theorem_name}_tbl"
    fn_name = f"{theorem_name}_set"
    pred = "IsGeomLineFree" if geometric else "IsLineFree"
    tbl = ", ".join("true" if x else "false" for x in res.indicator)
    return (
        f"private def {tbl_name} : List Bool := [{tbl}]\n\n"
        f"private def {fn_name}_idx (w : Word {d} {k}) : Nat :=\n"
        f"  (List.range {d}).foldl (fun acc i =>\n"
        f"    if hi : i < {d} then acc + (w ⟨i, hi⟩).val * {k} ^ i else acc) 0\n\n"
        f"private def {fn_name} (w : Word {d} {k}) : Bool :=\n"
        f"  {tbl_name}.getD ({fn_name}_idx w) false\n\n"
        f"theorem {theorem_name} : ∃ A : Word {d} {k} → Bool, {pred} A ∧ wordCard A = {sz} := by\n"
        f"  refine ⟨{fn_name}, ?_, ?_⟩\n"
        f"  · decide\n"
        f"  · decide\n"
    )


def emit_dhj_lower_lean(res: DHJSearchResult, theorem_name: str | None = None) -> str:
    """Emit a kernel-checked Lean 4 theorem proving `∃ A : Word d k → Bool, IsLineFree A ∧ wordCard A = M`."""
    name = theorem_name or f"dhj_{res.d}_{res.k}_ge_{res.size}"
    if res.fujimura_triples is not None and res.k == 3 and res.d >= 5:
        return emit_fujimura_lower_lean(res.d, res.fujimura_triples, res.size, theorem_name=name, geometric=False)
    return _emit_flat_table_lower_lean(res, name, geometric=False)


def emit_moser_lower_lean(res: DHJSearchResult, theorem_name: str | None = None) -> str:
    """Emit a kernel-checked Lean 4 theorem proving `∃ A : Word d 3 → Bool, IsGeomLineFree A ∧ wordCard A = M`."""
    name = theorem_name or f"moser_{res.d}_3_ge_{res.size}"
    if res.fujimura_triples is not None:
        return emit_fujimura_lower_lean(res.d, res.fujimura_triples, res.size, theorem_name=name, geometric=True)
    return _emit_flat_table_lower_lean(res, name, geometric=True)
