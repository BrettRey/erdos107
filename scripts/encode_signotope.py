#!/usr/bin/env python3
"""Encode signotope + canonical position constraints with no-n-gon avoidance.

This is an alternative to the full OM3 encoding. It uses:
- Orientation variables o(i,j,k) for i<j<k.
- Signotope axioms (forbid alternating patterns on 4-tuples).
- Canonical position symmetry breaking (optional).
- No-n-gon constraints via inside-triangle witnesses anchored at the leftmost
  vertex of each (n-1)-subset (triangulation trick).
"""

from __future__ import annotations

import argparse
import itertools
import json
from typing import Dict, List, Tuple

Clause = List[int]


def parity_from_sorted(sorted_vals: List[int], seq: List[int]) -> int:
    """Return parity (0=even,1=odd) of permutation from sorted_vals to seq."""
    pos = {v: i for i, v in enumerate(sorted_vals)}
    perm = [pos[x] for x in seq]
    inv = 0
    for i in range(len(perm)):
        for j in range(i + 1, len(perm)):
            if perm[i] > perm[j]:
                inv += 1
    return inv & 1


def add_xnor(clauses: List[Clause], p: int, x: int, y: int) -> None:
    # p <-> (x == y)  (XNOR)
    clauses.append([-p, -x, y])
    clauses.append([-p, -y, x])
    clauses.append([p, x, y])
    clauses.append([p, -x, -y])


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True, help="Convex n-gon size to avoid")
    ap.add_argument("--N", type=int, required=True, help="Number of points")
    ap.add_argument("--out", type=str, required=True, help="Output CNF path")
    ap.add_argument("--map-out", type=str, default="", help="Optional map JSON path")
    ap.add_argument("--canonical", action="store_true", help="Enable canonical position symmetry breaking")
    ap.add_argument("--fix-mirror", action="store_true", help="Fix an extra orientation to kill reflection")
    ap.add_argument("--gp3", action="store_true", help="Add 3-term Grassmann–Plücker relations")
    ap.add_argument("--no-avoid", action="store_true", help="Disable no-n-gon constraints")
    args = ap.parse_args()

    n = args.n
    N = args.N

    if n < 3 or N < 3 or n > N:
        raise SystemExit("Require 3 ≤ n ≤ N and 3 ≤ N.")

    # Variables: o(i,j,k) for i<j<k
    tri_var: Dict[Tuple[int, int, int], int] = {}
    next_var = 1
    for i in range(N):
        for j in range(i + 1, N):
            for k in range(j + 1, N):
                tri_var[(i, j, k)] = next_var
                next_var += 1

    def tri(i: int, j: int, k: int) -> int:
        if not (i < j < k):
            raise ValueError("tri() expects i<j<k")
        return tri_var[(i, j, k)]

    def ordered_lit(a: int, b: int, c: int) -> int:
        sorted_vals = sorted([a, b, c])
        var = tri(*sorted_vals)
        par = parity_from_sorted(sorted_vals, [a, b, c])
        return var if par == 0 else -var

    clauses: List[Clause] = []

    # Canonical position: fix o(0,i,j)=True for all 1<=i<j<=N-1
    if args.canonical:
        for i in range(1, N):
            for j in range(i + 1, N):
                clauses.append([ordered_lit(0, i, j)])
        if args.fix_mirror and N >= 4:
            clauses.append([ordered_lit(1, 2, 3)])

    # Signotope axioms: forbid alternating patterns on 4-tuples.
    # For each a<b<c<d, forbid (+ - + -) and (- + - +).
    for a in range(N):
        for b in range(a + 1, N):
            for c in range(b + 1, N):
                for d in range(c + 1, N):
                    s1 = ordered_lit(a, b, c)
                    s2 = ordered_lit(a, b, d)
                    s3 = ordered_lit(a, c, d)
                    s4 = ordered_lit(b, c, d)
                    clauses.append([-s1, s2, -s3, s4])
                    clauses.append([s1, -s2, s3, -s4])

    # 3-term Grassmann–Plücker relations (optional)
    if args.gp3:
        for a in range(N):
            others = [x for x in range(N) if x != a]
            for b, c, d, e in itertools.combinations(others, 4):
                p1 = next_var; next_var += 1
                p2 = next_var; next_var += 1
                p3 = next_var; next_var += 1
                add_xnor(clauses, p1, ordered_lit(a, b, c), ordered_lit(a, d, e))
                add_xnor(clauses, p2, ordered_lit(a, b, d), ordered_lit(a, c, e))
                add_xnor(clauses, p3, ordered_lit(a, b, e), ordered_lit(a, c, d))
                clauses.append([p1, -p2, p3])
                clauses.append([-p1, p2, -p3])

    # Inside-triangle variables and constraints
    inside_var: Dict[Tuple[int, int, int, int], int] = {}

    def inside(p: int, x1: int, a: int, b: int) -> int:
        # x1 < a < b by construction
        key = (p, x1, a, b)
        if key in inside_var:
            return inside_var[key]
        nonlocal next_var
        t = next_var
        next_var += 1
        inside_var[key] = t

        tri_lit = ordered_lit(x1, a, b)
        # Enforce t <-> (all three edge orientations match triangle orientation)
        e1 = next_var; next_var += 1
        e2 = next_var; next_var += 1
        e3 = next_var; next_var += 1
        add_xnor(clauses, e1, ordered_lit(x1, a, p), tri_lit)
        add_xnor(clauses, e2, ordered_lit(a, b, p), tri_lit)
        add_xnor(clauses, e3, ordered_lit(b, x1, p), tri_lit)
        clauses.append([-t, e1])
        clauses.append([-t, e2])
        clauses.append([-t, e3])
        clauses.append([-e1, -e2, -e3, t])
        return t

    # No-n-gon: for each n-set, at least one point is inside a triangulated triangle
    if not args.no_avoid:
        for subset in itertools.combinations(range(N), n):
            subset_list = list(subset)
            lits: List[int] = []
            for p in subset_list:
                others = [x for x in subset_list if x != p]
                x1 = min(others)
                rem = [x for x in others if x != x1]
                for a, b in itertools.combinations(rem, 2):
                    # Ensure x1 < a < b
                    if not (x1 < a < b):
                        a, b = sorted([a, b])
                    lits.append(inside(p, x1, a, b))
            clauses.append(lits)

    # Write CNF
    num_vars = next_var - 1
    with open(args.out, "w", encoding="utf-8") as fp:
        fp.write(f"p cnf {num_vars} {len(clauses)}\n")
        for cl in clauses:
            fp.write(" ".join(str(x) for x in cl) + " 0\n")

    if args.map_out:
        inv_tri = {v: k for k, v in tri_var.items()}
        inv_inside = {v: k for k, v in inside_var.items()}
        with open(args.map_out, "w", encoding="utf-8") as fp:
            json.dump(
                {
                    "tri": {str(v): list(inv_tri[v]) for v in sorted(inv_tri)},
                    "inside": {str(v): list(inv_inside[v]) for v in sorted(inv_inside)},
                },
                fp,
                indent=2,
            )


if __name__ == "__main__":
    main()
