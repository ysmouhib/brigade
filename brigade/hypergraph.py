"""General hypergraph Ramsey/VdW/Schur/Graph-Ramsey DPLL certifier, local-search finder,
structure analyzer, and Lean 4 code emitter.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import random
from typing import Any


@dataclass(frozen=True)
class HyperCertNode:
    """Node in a finite DPLL refutation tree compatible with `HJBrigade.HyperCert W r`."""

    kind: str  # "witness" | "split"
    witness: tuple[int, ...] | None = None
    color: int | None = None
    point: int | None = None
    branches: tuple[HyperCertNode, ...] = ()

    def size(self) -> int:
        """Total number of nodes in this subtree."""
        if self.kind == "witness":
            return 1
        return 1 + sum(child.size() for child in self.branches)

    def to_lean(self, witness_fmt: str = "pair", indent: int = 2) -> str:
        """Serialize into Lean 4 `HyperCert` expression syntax."""
        pad = " " * indent
        if self.kind == "witness":
            assert self.witness is not None and self.color is not None
            w_lit = _format_witness_lit(self.witness, witness_fmt)
            return f"{pad}HyperCert.witness {w_lit} {self.color}"
        assert self.point is not None
        inner = ",\n".join(b.to_lean(witness_fmt=witness_fmt, indent=indent + 2) for b in self.branches)
        return f"{pad}HyperCert.split {self.point} [\n{inner}\n{pad}]"

    def to_dict(self) -> dict[str, Any]:
        """Convert to a JSON-serializable dictionary."""
        if self.kind == "witness":
            return {"kind": "witness", "witness": list(self.witness or ()), "color": self.color}
        return {
            "kind": "split",
            "point": self.point,
            "branches": [b.to_dict() for b in self.branches],
        }


def _format_witness_lit(witness: tuple[int, ...], fmt: str) -> str:
    if fmt == "pair" and len(witness) == 2:
        return f"({witness[0]}, {witness[1]})"
    if fmt == "triple" and len(witness) == 3:
        return f"({witness[0]}, {witness[1]}, {witness[2]})"
    items = ", ".join(str(x) for x in witness)
    return f"({items})" if len(witness) > 1 else items


@dataclass
class HyperSolveResult:
    """Result returned by `solve_hypergraph`, `solve_vdw_cert`, `solve_schur`, or `solve_graph_ramsey`."""

    family: str
    params: dict[str, Any]
    n_vertices: int
    n_colors: int
    status: str  # "UNSAT_MONO" | "SAT_FREE" | "UNKNOWN"
    witness_coloring: list[int] | None = None
    witness_matrix: list[list[int]] | None = None
    cert_tree: HyperCertNode | None = None
    nodes_explored: int = 0
    edge_count: int = 0
    sym_broken: bool = False
    structure: dict[str, Any] = field(default_factory=dict)
    notes: str = ""


def _walksat_free_coloring(
    n_vertices: int,
    n_colors: int,
    edges: list[tuple[int, ...]],
    *,
    root_sym: int | None = 0,
    steps: int = 8000,
    restarts: int = 4,
    seed: int = 42,
) -> list[int] | None:
    """Fast local search for a hypergraph coloring with zero monochromatic edges."""
    if n_colors <= 0 or n_vertices <= 0:
        return None
    if not edges:
        return [0] * n_vertices

    uniq_edges = [tuple(dict.fromkeys(e)) for e in edges]
    v_to_edges: list[list[int]] = [[] for _ in range(n_vertices)]
    for ei, ue in enumerate(uniq_edges):
        if len(ue) <= 1:
            return None
        for v in ue:
            v_to_edges[v].append(ei)

    rng = random.Random(seed)

    for _ in range(max(1, restarts)):
        c = [rng.randrange(n_colors) for _ in range(n_vertices)]
        if root_sym is not None and 0 <= root_sym < n_vertices:
            c[root_sym] = 0

        def is_mono(ei: int) -> bool:
            ue = uniq_edges[ei]
            col0 = c[ue[0]]
            return all(c[v] == col0 for v in ue[1:])

        bad = {ei for ei in range(len(uniq_edges)) if is_mono(ei)}
        if not bad:
            return c

        for _step in range(steps):
            if not bad:
                return c
            ei = rng.choice(tuple(bad))
            ue = uniq_edges[ei]
            cands = [v for v in ue if v != root_sym] or list(ue)
            best_moves: list[tuple[int, int, int]] = []
            best_delta = 10**9
            for v in cands:
                old = c[v]
                for new_col in range(n_colors):
                    if new_col == old:
                        continue
                    c[v] = new_col
                    delta = 0
                    for ej in v_to_edges[v]:
                        was = ej in bad
                        now = is_mono(ej)
                        if now and not was:
                            delta += 1
                        elif was and not now:
                            delta -= 1
                    c[v] = old
                    if delta < best_delta:
                        best_delta = delta
                        best_moves = [(v, new_col, delta)]
                    elif delta == best_delta:
                        best_moves.append((v, new_col, delta))
            if not best_moves:
                continue
            if best_delta > 0 and rng.random() < 0.28:
                v_pick = rng.choice(cands)
                alts = [k for k in range(n_colors) if k != c[v_pick]]
                col_pick = rng.choice(alts) if alts else c[v_pick]
            else:
                v_pick, col_pick, _ = rng.choice(best_moves)
            c[v_pick] = col_pick
            for ej in v_to_edges[v_pick]:
                if is_mono(ej):
                    bad.add(ej)
                else:
                    bad.discard(ej)
        if not bad:
            return c
    return None


def verify_hypergraph_coloring(
    coloring: list[int],
    edges: list[tuple[int, ...]],
) -> tuple[bool, tuple[int, ...] | None]:
    """Return `(True, None)` if `coloring` has zero monochromatic edges, else `(False, first_bad)`."""
    for edge in edges:
        c0 = coloring[edge[0]]
        if all(coloring[v] == c0 for v in edge[1:]):
            return False, edge
    return True, None


def verify_hyper_cert(
    n_vertices: int,
    n_colors: int,
    valid_witnesses: dict[tuple[int, ...], tuple[int, ...]] | set[tuple[int, ...]],
    tree: HyperCertNode,
    assign: dict[int, int],
) -> bool:
    """Verify independently in Python that a `HyperCertNode` tree refutes all extensions."""
    if tree.kind == "witness":
        w = tree.witness
        col = tree.color
        if w is None or col is None or w not in valid_witnesses or not (0 <= col < n_colors):
            return False
        pts = valid_witnesses[w] if isinstance(valid_witnesses, dict) else w
        return all(assign.get(v) == col for v in pts)
    if tree.point is None or not (0 <= tree.point < n_vertices) or tree.point in assign:
        return False
    if len(tree.branches) != n_colors:
        return False
    for col, child in enumerate(tree.branches):
        nxt = dict(assign)
        nxt[tree.point] = col
        if not verify_hyper_cert(n_vertices, n_colors, valid_witnesses, child, nxt):
            return False
    return True


def solve_hypergraph(
    n_vertices: int,
    n_colors: int,
    raw_edges: list[tuple[int, ...]],
    edge_witnesses: list[tuple[int, ...]] | None = None,
    *,
    family: str = "hypergraph",
    params: dict[str, Any] | None = None,
    root_sym: int | None = 0,
    max_nodes: int = 250000,
    walksat_steps: int = 4000,
) -> HyperSolveResult:
    """Exact DPLL + MRV + unit-propagation + WalkSAT solver for finite hypergraph Ramsey bounds."""
    witnesses = edge_witnesses if edge_witnesses is not None else list(raw_edges)
    assert len(witnesses) == len(raw_edges)

    uniq_edges = [tuple(dict.fromkeys(e)) for e in raw_edges]
    p_info = dict(params or {})

    # 1. Fast WalkSAT check first if coloring could be satisfiable
    sat_candidate = _walksat_free_coloring(
        n_vertices,
        n_colors,
        uniq_edges,
        root_sym=root_sym,
        steps=walksat_steps,
        restarts=3,
    )
    if sat_candidate is not None:
        ok, _ = verify_hypergraph_coloring(sat_candidate, uniq_edges)
        if ok:
            struct = analyze_coloring_structure(sat_candidate, uniq_edges)
            return HyperSolveResult(
                family=family,
                params=p_info,
                n_vertices=n_vertices,
                n_colors=n_colors,
                status="SAT_FREE",
                witness_coloring=sat_candidate,
                edge_count=len(uniq_edges),
                sym_broken=root_sym is not None,
                structure=struct,
                notes="Verified free coloring found via local search.",
            )

    # 2. Exact DPLL with domain pruning & unit propagation
    if n_colors <= 0:
        return HyperSolveResult(
            family=family,
            params=p_info,
            n_vertices=n_vertices,
            n_colors=n_colors,
            status="UNKNOWN",
            notes="n_colors must be >= 1",
        )

    v_to_edges: list[list[int]] = [[] for _ in range(n_vertices)]
    for ei, ue in enumerate(uniq_edges):
        for v in ue:
            v_to_edges[v].append(ei)

    assign = [-1] * n_vertices
    nodes_explored = 0
    aborted = False
    found_coloring: list[int] | None = None

    def find_mono_witness(ei_candidates: list[int] | None = None) -> tuple[int, int] | None:
        indices = ei_candidates if ei_candidates is not None else range(len(uniq_edges))
        for ei in indices:
            ue = uniq_edges[ei]
            c0 = assign[ue[0]]
            if c0 != -1 and all(assign[v] == c0 for v in ue[1:]):
                return ei, c0
        return None

    def find_unit_forcing() -> tuple[int, int] | None:
        """Return `(unassigned_vertex, forbidden_color)` if an edge has k-1 equal-colored vertices."""
        best: tuple[int, int, int] | None = None
        for ei, ue in enumerate(uniq_edges):
            target_col = -1
            unassigned_v = -1
            unassigned_cnt = 0
            mixed = False
            for u in ue:
                au = assign[u]
                if au == -1:
                    unassigned_v = u
                    unassigned_cnt += 1
                    if unassigned_cnt > 1:
                        mixed = True
                        break
                elif target_col == -1:
                    target_col = au
                elif target_col != au:
                    mixed = True
                    break
            if not mixed and unassigned_cnt == 1 and target_col != -1:
                deg = len(v_to_edges[unassigned_v])
                if best is None or deg > best[2]:
                    best = (unassigned_v, target_col, deg)
        return (best[0], best[1]) if best is not None else None

    def pick_branch_var() -> int:
        best_v = -1
        best_key = (10**9, 0)
        for v in range(n_vertices):
            if assign[v] != -1:
                continue
            danger = 0
            for ei in v_to_edges[v]:
                ue = uniq_edges[ei]
                seen_col = -1
                ok_mono = True
                filled = 0
                for u in ue:
                    au = assign[u]
                    if au == -1:
                        continue
                    filled += 1
                    if seen_col == -1:
                        seen_col = au
                    elif seen_col != au:
                        ok_mono = False
                        break
                if ok_mono and filled > 0:
                    danger += 1 + filled * filled * 6
            key = (-danger - len(v_to_edges[v]), v)
            if key < best_key:
                best_key = key
                best_v = v
        return best_v

    def backtrack() -> tuple[HyperCertNode | None, set[int]]:
        nonlocal nodes_explored, aborted, found_coloring
        if nodes_explored >= max_nodes or found_coloring is not None:
            aborted = True
            return None, set()
        nodes_explored += 1

        if all(c != -1 for c in assign):
            found_coloring = list(assign)
            aborted = True
            return None, set()

        unit = find_unit_forcing()
        if unit is not None:
            best_v, bad_col = unit
            col_order = [bad_col, *[c for c in range(n_colors) if c != bad_col]]
        else:
            best_v = pick_branch_var()
            col_order = list(range(n_colors))

        if best_v == -1:
            found_coloring = list(assign)
            aborted = True
            return None, set()

        branches: list[HyperCertNode | None] = [None] * n_colors
        used_union: set[int] = set()

        for col in col_order:
            assign[best_v] = col
            hit = find_mono_witness(v_to_edges[best_v])
            if hit is not None:
                ei, hcol = hit
                node = HyperCertNode(kind="witness", witness=witnesses[ei], color=hcol)
                used = set(uniq_edges[ei])
                assign[best_v] = -1
                if best_v not in used:
                    return node, used
                branches[col] = node
                used_union |= used
                continue

            child, child_used = backtrack()
            assign[best_v] = -1
            if child is None:
                return None, set()
            if best_v not in child_used:
                return child, child_used
            branches[col] = child
            used_union |= child_used

        assert all(b is not None for b in branches)
        return HyperCertNode(kind="split", point=best_v, branches=tuple(b for b in branches if b is not None)), used_union

    sym_used = root_sym is not None and 0 <= root_sym < n_vertices
    if sym_used:
        assert root_sym is not None
        assign[root_sym] = 0
        hit_root = find_mono_witness(v_to_edges[root_sym])
        if hit_root is not None:
            ei, hcol = hit_root
            tree: HyperCertNode | None = HyperCertNode(kind="witness", witness=witnesses[ei], color=hcol)
        else:
            tree, _ = backtrack()
        assign[root_sym] = -1
    else:
        tree, _ = backtrack()

    if found_coloring is not None:
        ok, _ = verify_hypergraph_coloring(found_coloring, uniq_edges)
        if ok:
            return HyperSolveResult(
                family=family,
                params=p_info,
                n_vertices=n_vertices,
                n_colors=n_colors,
                status="SAT_FREE",
                witness_coloring=found_coloring,
                nodes_explored=nodes_explored,
                edge_count=len(uniq_edges),
                sym_broken=sym_used,
                structure=analyze_coloring_structure(found_coloring, uniq_edges),
                notes="Exact coloring found via DPLL.",
            )

    if tree is not None and not aborted:
        return HyperSolveResult(
            family=family,
            params=p_info,
            n_vertices=n_vertices,
            n_colors=n_colors,
            status="UNSAT_MONO",
            cert_tree=tree,
            nodes_explored=tree.size(),
            edge_count=len(uniq_edges),
            sym_broken=sym_used,
            notes=f"Exact {tree.size()}-node DPLL certificate.",
        )

    return HyperSolveResult(
        family=family,
        params=p_info,
        n_vertices=n_vertices,
        n_colors=n_colors,
        status="UNKNOWN",
        nodes_explored=nodes_explored,
        edge_count=len(uniq_edges),
        sym_broken=sym_used,
        notes=f"Search reached node budget ({max_nodes}) without full resolution.",
    )


def vdw_hyperedges(n: int, k: int) -> tuple[list[tuple[int, int]], list[tuple[int, ...]]]:
    """Generate `(a, d)` witnesses and vertex tuples `(a, a+d, ..., a+(k-1)d)` in `0..n-1`."""
    pairs: list[tuple[int, int]] = []
    edges: list[tuple[int, ...]] = []
    if k <= 1 or n < k:
        return pairs, edges
    for a in range(n):
        max_d = (n - 1 - a) // (k - 1)
        for d in range(1, max_d + 1):
            pairs.append((a, d))
            edges.append(tuple(a + j * d for j in range(k)))
    return pairs, edges


def solve_vdw_cert(
    n: int,
    k: int,
    r: int,
    *,
    root: int = 0,
    max_nodes: int = 250000,
    walksat_steps: int = 6000,
) -> HyperSolveResult:
    """Solve or certify `HasMonoAP n k r` (exact AP coloring or `HyperCert` refutation)."""
    pairs, edges = vdw_hyperedges(n, k)
    return solve_hypergraph(
        n,
        r,
        edges,
        edge_witnesses=pairs,
        family="vdw",
        params={"N": n, "k": k, "r": r, "root": root},
        root_sym=root if 0 <= root < n else None,
        max_nodes=max_nodes,
        walksat_steps=walksat_steps,
    )


def emit_vdw_cert_lean(
    res: HyperSolveResult,
    *,
    theorem_name: str | None = None,
) -> str:
    """Emit standalone Lean 4 theorem proving `HasMonoAP N k r` or `¬ HasMonoAP N k r`."""
    n = int(res.params["N"])
    k = int(res.params["k"])
    r = int(res.params["r"])
    root = int(res.params.get("root", 0))
    if res.status == "UNSAT_MONO" and res.cert_tree is not None:
        name = theorem_name or f"vdw_{k}_{r}_le_{n}"
        cert_name = f"private_cert_{name}"
        tree_str = res.cert_tree.to_lean(witness_fmt="pair", indent=2)
        return (
            f"private def {cert_name} : HyperCert (Nat × Nat) {r} :=\n"
            f"{tree_str}\n\n"
            f"theorem {name} : HasMonoAP {n} {k} {r} := by\n"
            f"  have h : checkHyperCert {n} {r} (vdwValidAP {n} {k}) (vdwAPPts {k}) {cert_name} [({root}, 0)] = true := by\n"
            f"    decide\n"
            f"  exact checkVdWCertSym_sound {n} {k} {r} (by decide) {root} (by decide) {cert_name} h\n"
        )
    if res.status == "SAT_FREE" and res.witness_coloring is not None:
        name = theorem_name or f"vdw_{k}_{r}_gt_{n}"
        w_name = f"private_witness_{name}"
        arr = ", ".join(str(x) for x in res.witness_coloring)
        return (
            f"private def {w_name} (i : Fin {n}) : Fin {r} :=\n"
            f"  ⟨([{arr}].getD i.val 0) % {r}, Nat.mod_lt _ (by decide)⟩\n\n"
            f"theorem {name} : ¬ HasMonoAP {n} {k} {r} := by\n"
            f"  intro h\n"
            f"  have hw : HasMonoAPFor {n} {k} {r} {w_name} := (hasMonoAP_iff_for {n} {k} {r}).mp h {w_name}\n"
            f"  revert hw\n"
            f"  decide\n"
        )
    raise ValueError(f"Cannot emit Lean proof for status={res.status!r}")


def schur_hyperedges(n: int) -> tuple[list[tuple[int, int, int]], list[tuple[int, ...]]]:
    """Generate 0-indexed `(x, y, z)` Schur triples satisfying `(x+1) + (y+1) = z+1`."""
    triples: list[tuple[int, int, int]] = []
    edges: list[tuple[int, ...]] = []
    for x in range(n):
        for y in range(x, n):
            z = x + y + 1
            if z < n:
                t = (x, y, z)
                triples.append(t)
                edges.append(tuple(dict.fromkeys(t)))
    return triples, edges


def solve_schur(
    n: int,
    r: int,
    *,
    root: int = 0,
    max_nodes: int = 250000,
    walksat_steps: int = 6000,
) -> HyperSolveResult:
    """Solve or certify `HasMonoSchur n r` on `{1, …, n}` with `r` colors."""
    triples, edges = schur_hyperedges(n)
    return solve_hypergraph(
        n,
        r,
        edges,
        edge_witnesses=triples,
        family="schur",
        params={"N": n, "r": r, "root": root},
        root_sym=root if 0 <= root < n else None,
        max_nodes=max_nodes,
        walksat_steps=walksat_steps,
    )


def emit_schur_lean(
    res: HyperSolveResult,
    *,
    theorem_name: str | None = None,
) -> str:
    """Emit standalone Lean 4 theorem proving `HasMonoSchur n r` or `¬ HasMonoSchur n r`."""
    n = int(res.params["N"])
    r = int(res.params["r"])
    root = int(res.params.get("root", 0))
    if res.status == "UNSAT_MONO" and res.cert_tree is not None:
        name = theorem_name or f"schur_{r}_le_{n}"
        cert_name = f"private_cert_{name}"
        tree_str = res.cert_tree.to_lean(witness_fmt="triple", indent=2)
        return (
            f"private def {cert_name} : HyperCert (Nat × Nat × Nat) {r} :=\n"
            f"{tree_str}\n\n"
            f"theorem {name} : HasMonoSchur {n} {r} := by\n"
            f"  have h : checkHyperCert {n} {r} (schurValidTriple {n}) schurTriplePts {cert_name} [({root}, 0)] = true := by\n"
            f"    decide\n"
            f"  exact checkSchurCertSym_sound {n} {r} (by decide) {root} (by decide) {cert_name} h\n"
        )
    if res.status == "SAT_FREE" and res.witness_coloring is not None:
        name = theorem_name or f"schur_{r}_gt_{n}"
        w_name = f"private_witness_{name}"
        arr = ", ".join(str(x) for x in res.witness_coloring)
        return (
            f"private def {w_name} (i : Fin {n}) : Fin {r} :=\n"
            f"  ⟨([{arr}].getD i.val 0) % {r}, Nat.mod_lt _ (by decide)⟩\n\n"
            f"theorem {name} : ¬ HasMonoSchur {n} {r} := by\n"
            f"  intro h\n"
            f"  have hw : HasMonoSchurFor {n} {r} {w_name} := (hasMonoSchur_iff_for {n} {r}).mp h {w_name}\n"
            f"  revert hw\n"
            f"  decide\n"
        )
    raise ValueError(f"Cannot emit Lean proof for status={res.status!r}")


def _check_matrix_cliques(matrix: list[list[int]], n: int, targets: list[int]) -> bool:
    """Return True iff `matrix` avoids a `targets[col]`-clique in every color `col`."""
    for col, k in enumerate(targets):
        if k <= 1:
            if n >= 1:
                return False
            continue
        adj = [[j for j in range(i + 1, n) if matrix[i][j] == col] for i in range(n)]

        def has_k(cands: list[int], need: int) -> bool:
            if need == 0:
                return True
            if len(cands) < need:
                return False
            for idx, v in enumerate(cands):
                if len(cands) - idx < need:
                    break
                nxt = [w for w in cands[idx + 1 :] if matrix[v][w] == col]
                if has_k(nxt, need - 1):
                    return True
            return False

        for u in range(n):
            if has_k(adj[u], k - 1):
                return False
    return True


def _try_circulant_graph_witness(n: int, targets: list[int]) -> list[list[int]] | None:
    """Try algebraic circulant / Paley colorings for 2-color or multicolor clique avoidance."""
    r = len(targets)
    if r == 2:
        # Try quadratic residues first when n is prime ≡ 1 (mod 4)
        if n > 2 and all(n % p != 0 for p in range(2, int(n**0.5) + 1)) and n % 4 == 1:
            qrs = {(a * a) % n for a in range(1, n)}
            mat = [[0 if i == j else (0 if (j - i) % n in qrs else 1) for j in range(n)] for i in range(n)]
            if _check_matrix_cliques(mat, n, targets):
                return mat
        # Enumerate symmetric zero-sets when n <= 16
        pairs = []
        seen = set()
        for d in range(1, n):
            if d in seen:
                continue
            opp = n - d
            seen.add(d)
            seen.add(opp)
            pairs.append((d, opp) if d != opp else (d,))
        if len(pairs) <= 14:
            for mask in range(1 << len(pairs)):
                red = set()
                for bi, grp in enumerate(pairs):
                    if (mask >> bi) & 1:
                        red.update(grp)
                mat = [[0 if i == j else (0 if (j - i) % n in red else 1) for j in range(n)] for i in range(n)]
                if _check_matrix_cliques(mat, n, targets):
                    return mat
    return None


def solve_graph_ramsey(
    n: int,
    s: int,
    t: int | None = None,
    *,
    r: int = 2,
    steps: int = 12000,
    seed: int = 42,
) -> HyperSolveResult:
    """Search for a clique-avoiding edge coloring on `n` vertices for `R(s, t)` or `R_r(s)`."""
    if t is not None and r == 2:
        targets = [s, t]
        params: dict[str, Any] = {"N": n, "s": s, "t": t, "r": 2}
    else:
        targets = [s] * r
        params = {"N": n, "r": r, "k": s}

    # Try fast algebraic circulant first
    mat = _try_circulant_graph_witness(n, targets)
    if mat is not None:
        return HyperSolveResult(
            family="ramsey",
            params=params,
            n_vertices=n,
            n_colors=len(targets),
            status="SAT_FREE",
            witness_matrix=mat,
            edge_count=n * (n - 1) // 2,
            notes="Algebraic circulant/Paley witness verified clique-free.",
        )

    # General pair-hypergraph WalkSAT over K_n edges
    pair_idx: dict[tuple[int, int], int] = {}
    pairs_list: list[tuple[int, int]] = []
    for u in range(n):
        for v in range(u + 1, n):
            pair_idx[(u, v)] = len(pairs_list)
            pairs_list.append((u, v))

    if r == 2 and s != t:
        # Asymmetric clique constraints: encode directly in random local search on edges
        rng = random.Random(seed)
        from itertools import combinations

        cliques_0 = [tuple(pair_idx[a] for a in combinations(verts, 2)) for verts in combinations(range(n), s)]
        cliques_1 = [tuple(pair_idx[a] for a in combinations(verts, 2)) for verts in combinations(range(n), t or s)]
        m = len(pairs_list)
        if m > 0:
            e_to_0: list[list[int]] = [[] for _ in range(m)]
            e_to_1: list[list[int]] = [[] for _ in range(m)]
            for ci, clq in enumerate(cliques_0):
                for ei in clq:
                    e_to_0[ei].append(ci)
            for ci, clq in enumerate(cliques_1):
                for ei in clq:
                    e_to_1[ei].append(ci)
            c = [rng.randrange(2) for _ in range(m)]
            bad0 = {ci for ci, clq in enumerate(cliques_0) if all(c[e] == 0 for e in clq)}
            bad1 = {ci for ci, clq in enumerate(cliques_1) if all(c[e] == 1 for e in clq)}
            for _ in range(steps):
                if not bad0 and not bad1:
                    w_mat = [[0] * n for _ in range(n)]
                    for idx, (u, v) in enumerate(pairs_list):
                        w_mat[u][v] = c[idx]
                        w_mat[v][u] = c[idx]
                    return HyperSolveResult(
                        family="ramsey",
                        params=params,
                        n_vertices=n,
                        n_colors=2,
                        status="SAT_FREE",
                        witness_matrix=w_mat,
                        edge_count=m,
                        notes="Clique-avoiding coloring found via edge WalkSAT.",
                    )
                pick_from_0 = bool(bad0) and (not bad1 or rng.random() < 0.5)
                if pick_from_0:
                    ci = rng.choice(tuple(bad0))
                    cand_edges = cliques_0[ci]
                else:
                    ci = rng.choice(tuple(bad1))
                    cand_edges = cliques_1[ci]
                e_flip = rng.choice(cand_edges)
                c[e_flip] = 1 - c[e_flip]
                for cj in e_to_0[e_flip]:
                    if all(c[e] == 0 for e in cliques_0[cj]):
                        bad0.add(cj)
                    else:
                        bad0.discard(cj)
                for cj in e_to_1[e_flip]:
                    if all(c[e] == 1 for e in cliques_1[cj]):
                        bad1.add(cj)
                    else:
                        bad1.discard(cj)
    else:
        from itertools import combinations

        k_mono = s
        edges = [tuple(pair_idx[a] for a in combinations(verts, 2)) for verts in combinations(range(n), k_mono)]
        sat = _walksat_free_coloring(len(pairs_list), r, edges, root_sym=None, steps=steps, restarts=3, seed=seed)
        if sat is not None:
            w_mat = [[0] * n for _ in range(n)]
            for idx, (u, v) in enumerate(pairs_list):
                w_mat[u][v] = sat[idx]
                w_mat[v][u] = sat[idx]
            return HyperSolveResult(
                family="ramsey",
                params=params,
                n_vertices=n,
                n_colors=r,
                status="SAT_FREE",
                witness_matrix=w_mat,
                edge_count=len(pairs_list),
                notes="Multicolor clique-avoiding coloring found via WalkSAT.",
            )

    return HyperSolveResult(
        family="ramsey",
        params=params,
        n_vertices=n,
        n_colors=len(targets),
        status="UNKNOWN",
        edge_count=n * (n - 1) // 2,
        notes="No clique-avoiding witness found within search budget.",
    )


def emit_graph_ramsey_lower_lean(
    res: HyperSolveResult,
    *,
    theorem_name: str | None = None,
) -> str:
    """Emit Lean 4 lower-bound witness theorem using `checkNoClique_sound` / `checkNoMonoClique_sound`."""
    if res.status != "SAT_FREE" or res.witness_matrix is None:
        raise ValueError(f"Expected SAT_FREE matrix witness, got status={res.status!r}")
    n = int(res.params["N"])
    r = int(res.params.get("r", res.n_colors))
    mat = res.witness_matrix
    w_name = f"private_graph_{theorem_name or f'r_{n}'}"
    if r == 2 and "s" in res.params and "t" in res.params:
        s = int(res.params["s"])
        t = int(res.params["t"])
        name = theorem_name or f"ramsey_{s}_{t}_gt_{n}"
        bool_rows = ",\n    ".join("[" + ", ".join("true" if x else "false" for x in row) + "]" for row in mat)
        return (
            f"private def {w_name}_table : List (List Bool) :=\n  [\n    {bool_rows}\n  ]"
            + f"\n\nprivate def {w_name} (u v : Fin {n}) : Bool :=\n"
            f"  ({w_name}_table.getD u.val []).getD v.val false\n\n"
            f"theorem {name} : ¬ GraphRamseyUpper {n} {s} {t} :=\n"
            f"  checkNoClique_sound {w_name} (by decide) (by decide)\n"
        )
    rows = ",\n    ".join("[" + ", ".join(str(x) for x in row) + "]" for row in mat)
    k = int(res.params.get("k", res.params.get("s", 3)))
    name = theorem_name or f"ramsey_mono_{r}_{k}_gt_{n}"
    return (
        f"private def {w_name}_table : List (List Nat) :=\n  [\n    {rows}\n  ]\n\n"
        f"private def {w_name} (u v : Fin {n}) : Fin {r} :=\n"
        f"  ⟨(({w_name}_table.getD u.val []).getD v.val 0) % {r}, Nat.mod_lt _ (by decide)⟩\n\n"
        f"theorem {name} : ¬ MulticolorRamseyUpper {n} {r} {k} :=\n"
        f"  checkNoMonoClique_sound {w_name} (by decide)\n"
    )


def analyze_coloring_structure(
    coloring: list[int],
    hyperedges: list[tuple[int, ...]] | None = None,
) -> dict[str, Any]:
    """Summarize symmetries, periods, color distribution, and critical edges of a witness coloring."""
    n = len(coloring)
    if n == 0:
        return {"length": 0}
    counts: dict[int, int] = {}
    for col in coloring:
        counts[col] = counts.get(col, 0) + 1
    pal_matches = sum(1 for i in range(n) if coloring[i] == coloring[n - 1 - i])
    best_period = None
    best_period_rate = 0.0
    for p in range(1, max(2, n // 2 + 1)):
        if n - p <= 0:
            continue
        rate = sum(1 for i in range(n - p) if coloring[i] == coloring[i + p]) / (n - p)
        if rate > best_period_rate:
            best_period_rate = rate
            best_period = p

    critical_edges = 0
    if hyperedges:
        for e in hyperedges:
            cols = {coloring[v] for v in e}
            if len(cols) <= 2:
                critical_edges += 1

    return {
        "length": n,
        "color_counts": counts,
        "palindrome_ratio": round(pal_matches / n, 4),
        "is_palindrome": pal_matches == n,
        "best_period": best_period,
        "best_period_ratio": round(best_period_rate, 4),
        "near_mono_edges": critical_edges,
    }
