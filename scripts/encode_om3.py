#!/usr/bin/env python3
from __future__ import annotations

import argparse
import itertools
import json
from typing import Dict, List, Tuple


Clause = List[int]


def alt_sigma(i: int, j: int, k: int) -> bool:
    # True iff (i,j,k) is in cyclic increasing order
    return (i < j and j < k) or (j < k and k < i) or (k < i and i < j)


def add_equiv(clauses: List[Clause], x: int, y: int) -> None:
    # x <-> y
    clauses.append([-x, y])
    clauses.append([x, -y])


def add_equiv_not(clauses: List[Clause], x: int, y: int) -> None:
    # x <-> ¬y
    clauses.append([x, y])
    clauses.append([-x, -y])


def add_xnor(clauses: List[Clause], p: int, x: int, y: int) -> None:
    # p <-> (x == y)  (XNOR)
    clauses.append([-p, -x, y])
    clauses.append([-p, -y, x])
    clauses.append([p, x, y])
    clauses.append([p, -x, -y])


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--N", type=int, required=True)
    ap.add_argument("--out", type=str, required=True)
    ap.add_argument("--map-out", type=str, default="")
    args = ap.parse_args()

    n = args.n
    N = args.N

    if n < 3 or N < 3 or n > N:
        raise SystemExit("Require 3 ≤ n ≤ N and 3 ≤ N.")

    # Variables: sigma(a,b,c) for all ordered triples of distinct indices in [0..N-1].
    sigma_var: Dict[Tuple[int, int, int], int] = {}
    next_var = 1
    for a in range(N):
        for b in range(N):
            if b == a:
                continue
            for c in range(N):
                if c == a or c == b:
                    continue
                sigma_var[(a, b, c)] = next_var
                next_var += 1

    def sigma(a: int, b: int, c: int) -> int:
        return sigma_var[(a, b, c)]

    clauses: List[Clause] = []

    # OrderType axioms: swap12 and cycle.
    # swap12: σ(a,b,c) = ¬σ(b,a,c)
    for a in range(N):
        for b in range(a + 1, N):
            for c in range(N):
                if c == a or c == b:
                    continue
                add_equiv_not(clauses, sigma(a, b, c), sigma(b, a, c))

    # cycle: σ(a,b,c) = σ(b,c,a) and σ(b,c,a) = σ(c,a,b) for each unordered triple
    for a in range(N):
        for b in range(a + 1, N):
            for c in range(b + 1, N):
                x = sigma(a, b, c)
                y = sigma(b, c, a)
                z = sigma(c, a, b)
                add_equiv(clauses, x, y)
                add_equiv(clauses, y, z)

    # IsChirotope: Grassmann–Plücker relation for all ordered 5-tuples of distinct indices.
    # (This is the "full" version; it blows up fast, but is perfect for small tests.)
    for a, b, c, d, e in itertools.permutations(range(N), 5):
        # p1 = (σ(a,b,c) == σ(a,d,e))
        # p2 = (σ(a,b,d) == σ(a,c,e))
        # p3 = (σ(a,b,e) == σ(a,c,d))
        p1 = next_var; next_var += 1
        p2 = next_var; next_var += 1
        p3 = next_var; next_var += 1

        add_xnor(clauses, p1, sigma(a, b, c), sigma(a, d, e))
        add_xnor(clauses, p2, sigma(a, b, d), sigma(a, c, e))
        add_xnor(clauses, p3, sigma(a, b, e), sigma(a, c, d))

        # not all equal: exclude TTT and FFF
        clauses.append([p1, p2, p3])
        clauses.append([-p1, -p2, -p3])

    # AvoidsAlternating: for every injection f : Fin n ↪ Fin N, not(IsAlternating(reindex σ f))
    # Encode ¬(∀ distinct i,j,k : σ(f(i),f(j),f(k)) == alt(i,j,k)) as one big mismatch clause.
    for inj in itertools.permutations(range(N), n):
        def f(i: int) -> int:
            return inj[i]

        mismatch_lits: List[int] = []
        for i in range(n):
            for j in range(n):
                if j == i:
                    continue
                for k in range(n):
                    if k == i or k == j:
                        continue
                    expected = alt_sigma(i, j, k)
                    x = sigma(f(i), f(j), f(k))
                    # mismatch literal is (x != expected)
                    mismatch_lits.append(-x if expected else x)

        clauses.append(mismatch_lits)

    num_vars = next_var - 1
    num_clauses = len(clauses)

    with open(args.out, "w", encoding="utf-8") as fp:
        fp.write(f"p cnf {num_vars} {num_clauses}\n")
        for cl in clauses:
            fp.write(" ".join(str(l) for l in cl) + " 0\n")

    if args.map_out:
        # Only the sigma variables; aux vars are unnamed
        inv = {v: k for k, v in sigma_var.items()}
        with open(args.map_out, "w", encoding="utf-8") as fp:
            json.dump({"sigma": {str(v): inv[v] for v in sorted(inv)}}, fp, indent=2)

    print(f"Wrote {args.out}")
    print(f"vars={num_vars} clauses={num_clauses}")


if __name__ == "__main__":
    main()
