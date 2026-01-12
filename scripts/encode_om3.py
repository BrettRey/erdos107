#!/usr/bin/env python3
from __future__ import annotations

import argparse
import itertools
import json
import subprocess
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


def write_dimacs(path: str, num_vars: int, clauses: List[Clause]) -> None:
    with open(path, "w", encoding="utf-8") as fp:
        fp.write(f"p cnf {num_vars} {len(clauses)}\n")
        for cl in clauses:
            fp.write(" ".join(str(l) for l in cl) + " 0\n")


def run_cadical(cnf_path: str, plain: bool = False) -> Tuple[str, Dict[int, bool]]:
    cmd = ["cadical", "-q"]
    if plain:
        cmd.append("--plain")
    cmd.append(cnf_path)
    p = subprocess.run(cmd, capture_output=True, text=True)
    if p.returncode == 20:
        return "UNSAT", {}
    if p.returncode != 10:
        return "ERROR", {}

    assign: Dict[int, bool] = {}
    for line in p.stdout.splitlines():
        if not line.startswith("v"):
            continue
        for tok in line.split()[1:]:
            lit = int(tok)
            if lit == 0:
                continue
            assign[abs(lit)] = (lit > 0)
    return "SAT", assign


def iter_bits(mask: int):
    while mask:
        lsb = mask & -mask
        yield (lsb.bit_length() - 1)
        mask ^= lsb


def find_alternating_sequence(N: int, n: int, sigma_var, assign: Dict[int, bool]) -> List[int] | None:
    if N <= 10:
        for seq in itertools.permutations(range(N), n):
            if seq[0] != min(seq):
                continue
            ok = True
            for i in range(n):
                for j in range(i + 1, n):
                    for k in range(j + 1, n):
                        v = sigma_var[(seq[i], seq[j], seq[k])]
                        if not assign.get(v, False):
                            ok = False
                            break
                    if not ok:
                        break
                if not ok:
                    break
            if ok:
                return list(seq)
        return None

    # Precompute pos[a][b] bitmask of c with σ(a,b,c)=True.
    pos = [[0] * N for _ in range(N)]
    for a in range(N):
        for b in range(N):
            if a == b:
                continue
            m = 0
            for c in range(N):
                if c == a or c == b:
                    continue
                v = sigma_var[(a, b, c)]
                if assign.get(v, False):
                    m |= (1 << c)
            pos[a][b] = m

    def backtrack(seq: List[int], used: int, pair_mask: int) -> List[int] | None:
        if len(seq) == n:
            return seq
        cand = pair_mask & ~used
        if cand.bit_count() < (n - len(seq)):
            return None
        for x in iter_bits(cand):
            new_used = used | (1 << x)
            new_pair = pair_mask
            for v in seq:
                new_pair &= pos[v][x]
                if new_pair == 0:
                    break
            else:
                res = backtrack(seq + [x], new_used, new_pair)
                if res is not None:
                    return res
        return None

    for v0 in range(N):
        used0 = 1 << v0
        for v1 in range(N):
            if v1 == v0:
                continue
            used1 = used0 | (1 << v1)
            pair_mask = pos[v0][v1]
            cand2 = pair_mask & ~used1
            for v2 in iter_bits(cand2):
                used2 = used1 | (1 << v2)
                pair2 = pair_mask & pos[v0][v2] & pos[v1][v2]
                res = backtrack([v0, v1, v2], used2, pair2)
                if res is not None:
                    return res
    return None


def canonical_rotate_min(seq: List[int]) -> List[int]:
    m = min(seq)
    r = seq.index(m)
    return seq[r:] + seq[:r]


def find_alternating_orders_batch_large(
    N: int,
    n: int,
    sigma_var,
    assign: Dict[int, bool],
    limit: int,
    blocked_orders: set[Tuple[int, ...]],
) -> List[List[int]]:
    # Precompute pos[a][b] bitmask of c with σ(a,b,c)=True.
    pos = [[0] * N for _ in range(N)]
    for a in range(N):
        for b in range(N):
            if a == b:
                continue
            m = 0
            for c in range(N):
                if c == a or c == b:
                    continue
                v = sigma_var[(a, b, c)]
                if assign.get(v, False):
                    m |= (1 << c)
            pos[a][b] = m

    out: List[List[int]] = []
    seen: set[Tuple[int, ...]] = set()

    def emit(seq: List[int]) -> None:
        if len(out) >= limit:
            return
        seq = canonical_rotate_min(seq)
        key = tuple(seq)
        if key in blocked_orders or key in seen:
            return
        seen.add(key)
        out.append(seq)

    def backtrack(seq: List[int], used: int, pair_mask: int) -> None:
        if len(out) >= limit:
            return
        if len(seq) == n:
            emit(seq)
            return
        cand = pair_mask & ~used
        if cand.bit_count() < (n - len(seq)):
            return
        for x in iter_bits(cand):
            new_used = used | (1 << x)
            new_pair = pair_mask
            for v in seq:
                new_pair &= pos[v][x]
                if new_pair == 0:
                    break
            else:
                backtrack(seq + [x], new_used, new_pair)
                if len(out) >= limit:
                    return

    for v0 in range(N):
        used0 = 1 << v0
        for v1 in range(N):
            if v1 == v0:
                continue
            used1 = used0 | (1 << v1)
            pair_mask = pos[v0][v1]
            cand2 = pair_mask & ~used1
            for v2 in iter_bits(cand2):
                used2 = used1 | (1 << v2)
                pair2 = pair_mask & pos[v0][v2] & pos[v1][v2]
                backtrack([v0, v1, v2], used2, pair2)
                if len(out) >= limit:
                    return out

    return out


def find_alternating_sets_small(
    N: int,
    n: int,
    sigma_var,
    assign: Dict[int, bool],
    blocked_sets: set[Tuple[int, ...]],
    limit: int,
) -> List[List[int]]:
    out: List[List[int]] = []
    seen: set[Tuple[int, ...]] = set()
    for seq in itertools.permutations(range(N), n):
        if seq[0] != min(seq):
            continue
        subset = tuple(sorted(seq))
        if subset in blocked_sets or subset in seen:
            continue
        ok = True
        for i in range(n):
            for j in range(i + 1, n):
                for k in range(j + 1, n):
                    v = sigma_var[(seq[i], seq[j], seq[k])]
                    if not assign.get(v, False):
                        ok = False
                        break
                if not ok:
                    break
            if not ok:
                break
        if ok:
            seen.add(subset)
            out.append(list(seq))
            if limit != 0 and len(out) >= limit:
                break
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--N", type=int, required=True)
    ap.add_argument("--out", type=str, required=True)
    ap.add_argument("--map-out", type=str, default="")
    ap.add_argument("--acyclic", action="store_true")
    ap.add_argument("--lazy", action="store_true")
    ap.add_argument("--max-iters", type=int, default=500)
    ap.add_argument("--block-set", action="store_true")
    ap.add_argument(
        "--batch",
        type=int,
        default=0,
        help="Lazy mode: number of distinct alternating n-sets to block per SAT model (0 = block all found).",
    )
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

    # Symmetry breaker: fix one triple orientation
    if N >= 3:
        clauses.append([sigma(0, 1, 2)])

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

    # Acyclicity (optional): for every ordered quadruple (a,b,c,d),
    # ¬X_abc ∨ X_dbc ∨ X_adc ∨ X_abd
    if args.acyclic:
        for a, b, c, d in itertools.permutations(range(N), 4):
            clauses.append([-sigma(a, b, c), sigma(d, b, c), sigma(a, d, c), sigma(a, b, d)])

    # IsChirotope: Grassmann–Plücker relation (pivot + 4-combination form).
    for a in range(N):
        others = [x for x in range(N) if x != a]
        for b, c, d, e in itertools.combinations(others, 4):
            # p1 = (σ(a,b,c) == σ(a,d,e))
            # p2 = (σ(a,b,d) == σ(a,c,e))  [sign-flipped in GPRel]
            # p3 = (σ(a,b,e) == σ(a,c,d))
            p1 = next_var; next_var += 1
            p2 = next_var; next_var += 1
            p3 = next_var; next_var += 1

            add_xnor(clauses, p1, sigma(a, b, c), sigma(a, d, e))
            add_xnor(clauses, p2, sigma(a, b, d), sigma(a, c, e))
            add_xnor(clauses, p3, sigma(a, b, e), sigma(a, c, d))

            # not all equal for (p1, ¬p2, p3): exclude TTT and FFF
            clauses.append([p1, -p2, p3])
            clauses.append([-p1, p2, -p3])

    # AvoidsAlternating: for every injection f : Fin n ↪ Fin N, not(IsAlternating(reindex σ f))
    # Encode ¬(∀ distinct i,j,k : σ(f(i),f(j),f(k)) == alt(i,j,k)) as one big mismatch clause.
    if not args.lazy:
        for inj in itertools.permutations(range(N), n):
            def f(i: int) -> int:
                return inj[i]

            mismatch_lits: List[int] = []
            for i in range(n):
                for j in range(i + 1, n):
                    for k in range(j + 1, n):
                        # For i<j<k, alt_sigma(i,j,k) is always True.
                        x = sigma(f(i), f(j), f(k))
                        # mismatch literal is (x != True) -> ¬x
                        mismatch_lits.append(-x)

            clauses.append(mismatch_lits)

    if args.map_out:
        # Only the sigma variables; aux vars are unnamed
        inv = {v: k for k, v in sigma_var.items()}
        with open(args.map_out, "w", encoding="utf-8") as fp:
            json.dump({"sigma": {str(v): inv[v] for v in sorted(inv)}}, fp, indent=2)

    num_vars = next_var - 1

    if args.lazy:
        blocked_sets = set()
        blocked_orders = set()

        def make_block(order: List[int]) -> Clause:
            block: Clause = []
            for i in range(n):
                for j in range(i + 1, n):
                    for k in range(j + 1, n):
                        block.append(-sigma_var[(order[i], order[j], order[k])])
            return block

        for it in range(args.max_iters):
            write_dimacs(args.out, num_vars, clauses)
            status, assign = run_cadical(args.out, plain=True)
            if status == "UNSAT":
                print(f"UNSAT after {it} blocking clauses")
                return
            if status != "SAT":
                raise SystemExit("Solver error")

            missing = [v for v in sigma_var.values() if v not in assign]
            if missing:
                raise SystemExit(f"Model missing {len(missing)} sigma vars; cannot trust search.")

            if N <= 10:
                seqs = find_alternating_sets_small(N, n, sigma_var, assign, blocked_sets, args.batch)
            else:
                lim = args.batch if args.batch != 0 else 1
                seqs = find_alternating_orders_batch_large(
                    N, n, sigma_var, assign, lim, blocked_orders
                )

            if not seqs:
                print("SAT and no alternating subset found -> OM3Counterexample candidate")
                return

            new_sets = 0
            new_orders = 0
            for seq in seqs:
                seq = canonical_rotate_min(seq)
                subset = tuple(sorted(seq))
                if args.block_set:
                    if subset in blocked_sets:
                        continue
                    blocked_sets.add(subset)
                    new_sets += 1
                    m = subset[0]
                    rest = list(subset[1:])
                    for perm in itertools.permutations(rest):
                        clauses.append(make_block([m, *perm]))
                else:
                    order = tuple(seq)
                    if order in blocked_orders:
                        continue
                    blocked_orders.add(order)
                    clauses.append(make_block(seq))
                    new_orders += 1

            if args.block_set:
                print(
                    f"iter {it + 1}: blocked {new_sets} set(s); total blocked sets={len(blocked_sets)}"
                )
            else:
                print(
                    f"iter {it + 1}: blocked {new_orders} order(s); total blocked orders={len(blocked_orders)}"
                )

        print(f"Reached max-iters={args.max_iters} without UNSAT or counterexample")
        return

    write_dimacs(args.out, num_vars, clauses)
    print(f"Wrote {args.out}")
    print(f"vars={num_vars} clauses={len(clauses)}")


if __name__ == "__main__":
    main()
