"""Density Hales-Jewett solver (exact branch-and-bound + tabu local search) & Lean witness compiler."""

from __future__ import annotations

from dataclasses import dataclass
import random
import time

from .skeptic_hj import encode_word, generate_lines


@dataclass
class DHJSearchResult:
    d: int
    k: int
    num_words: int
    size: int
    optimal: bool
    indicator: list[int]
    elapsed_s: float


def _check_line_free(indicator: list[int], lines: list[tuple[tuple[int | None, ...], tuple[int, ...]]]) -> bool:
    for _, pts in lines:
        if all(indicator[p] == 1 for p in pts):
            return False
    return True


def _solve_dhj_exact(d: int, k: int, num_words: int, lines: list[tuple[tuple[int | None, ...], tuple[int, ...]]]) -> list[int]:
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
        can_take = True
        for li in pt_lines[p]:
            if line_cnt[li] == k - 1:
                can_take = False
                break
        if can_take:
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
    lines: list[tuple[tuple[int | None, ...], tuple[int, ...]]],
    restarts: int = 30,
    steps: int = 1200,
    seed: int = 42,
) -> list[int]:
    rng = random.Random(seed)
    pt_lines: list[list[int]] = [[] for _ in range(num_words)]
    for li, (_, pts) in enumerate(lines):
        for p in pts:
            pt_lines[p].append(li)

    best_ind: list[int] = []
    best_size = -1

    for restart in range(restarts):
        ind = [0] * num_words
        line_cnt = [0] * len(lines)
        cur_size = 0

        # Prioritize middle-weight / balanced words in half of restarts, random in others
        perm = list(range(num_words))
        rng.shuffle(perm)
        if restart % 2 == 0 and k >= 3:
            # Prefer words with balanced counts of letters (strong heuristic for DHJ)
            def balance_score(idx: int) -> tuple[int, float]:
                coords = []
                c = idx
                for _ in range(d):
                    coords.append(c % k)
                    c //= k
                counts = [coords.count(t) for t in range(k)]
                spread = max(counts) - min(counts)
                return (spread, rng.random())

            perm.sort(key=balance_score)

        for p in perm:
            if all(line_cnt[li] < k - 1 for li in pt_lines[p]):
                ind[p] = 1
                cur_size += 1
                for li in pt_lines[p]:
                    line_cnt[li] += 1

        # Randomized (1-out, k-in) local search: remove 1 element (or 2), greedily pack
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


def solve_dhj(d: int, k: int, restarts: int = 30, steps: int = 1200) -> DHJSearchResult:
    """Find a maximum (exact for small `k^d <= 27`, heuristic otherwise) line-free subset of `[k]^d`."""
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
        ind = _solve_dhj_exact(d, k, num_words, lines)
        return DHJSearchResult(
            d=d, k=k, num_words=num_words, size=sum(ind),
            optimal=True, indicator=ind, elapsed_s=time.perf_counter() - t0,
        )
    ind = _local_search_dhj(d, k, num_words, lines, restarts=restarts, steps=steps)
    return DHJSearchResult(
        d=d, k=k, num_words=num_words, size=sum(ind),
        optimal=False, indicator=ind, elapsed_s=time.perf_counter() - t0,
    )


def emit_dhj_lower_lean(res: DHJSearchResult, theorem_name: str | None = None) -> str:
    """Emit a kernel-checked Lean 4 theorem proving `∃ A : Word d k → Bool, IsLineFree A ∧ wordCard A = M`."""
    name = theorem_name or f"dhj_{res.d}_{res.k}_ge_{res.size}"
    d, k, sz = res.d, res.k, res.size
    tbl_name = f"{name}_tbl"
    fn_name = f"{name}_set"
    tbl = ", ".join("true" if x else "false" for x in res.indicator)
    return (
        f"private def {tbl_name} : List Bool := [{tbl}]\n\n"
        f"private def {fn_name}_idx (w : Word {d} {k}) : Nat :=\n"
        f"  (List.range {d}).foldl (fun acc i =>\n"
        f"    if hi : i < {d} then acc + (w ⟨i, hi⟩).val * {k} ^ i else acc) 0\n\n"
        f"private def {fn_name} (w : Word {d} {k}) : Bool :=\n"
        f"  {tbl_name}.getD ({fn_name}_idx w) false\n\n"
        f"theorem {name} : ∃ A : Word {d} {k} → Bool, IsLineFree A ∧ wordCard A = {sz} := by\n"
        f"  refine ⟨{fn_name}, ?_, ?_⟩\n"
        f"  · decide\n"
        f"  · decide\n"
    )
