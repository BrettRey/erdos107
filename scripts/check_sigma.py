#!/usr/bin/env python3
from __future__ import annotations

import argparse
import itertools
import json
from typing import Dict, List, Tuple


def iter_bits(mask: int):
    while mask:
        lsb = mask & -mask
        yield (lsb.bit_length() - 1)
        mask ^= lsb


def find_alternating_sequence(N: int, n: int, sigma: Dict[Tuple[int, int, int], bool]) -> List[int] | None:
    if N <= 10:
        for seq in itertools.permutations(range(N), n):
            if seq[0] != min(seq):
                continue
            ok = True
            for i in range(n):
                for j in range(i + 1, n):
                    for k in range(j + 1, n):
                        if not sigma[(seq[i], seq[j], seq[k])]:
                            ok = False
                            break
                    if not ok:
                        break
                if not ok:
                    break
            if ok:
                return list(seq)
        return None

    pos = [[0] * N for _ in range(N)]
    for a in range(N):
        for b in range(N):
            if a == b:
                continue
            m = 0
            for c in range(N):
                if c == a or c == b:
                    continue
                if sigma[(a, b, c)]:
                    m |= (1 << c)
            pos[a][b] = m

    def backtrack(seq: List[int], used: int, pair_mask: int) -> List[int] | None:
        if len(seq) == n:
            return seq
        cand = pair_mask & ~used
        if cand.bit_count() < (n - len(seq)):
            return None
        for x in iter_bits(cand):
            if len(seq) + 1 == n:
                return seq + [x]
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


def load_sigma(path: str) -> Tuple[int, int, Dict[Tuple[int, int, int], bool]]:
    with open(path, "r", encoding="utf-8") as fp:
        data = json.load(fp)
    if "sigma" not in data:
        raise SystemExit("JSON missing 'sigma'")
    N = int(data["N"])
    n = int(data["n"])
    sigma_raw = data["sigma"]
    sigma: Dict[Tuple[int, int, int], bool] = {}
    for k, v in sigma_raw.items():
        a, b, c = (int(x) for x in k.split(","))
        sigma[(a, b, c)] = bool(v)
    return N, n, sigma


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", required=True, help="Sigma JSON path (from encode_om3.py --dump-sigma)")
    ap.add_argument("--n", type=int, default=None, help="Optional n override")
    ap.add_argument("--N", type=int, default=None, help="Optional N override")
    args = ap.parse_args()

    N, n, sigma = load_sigma(args.json)
    if args.N is not None and args.N != N:
        raise SystemExit(f"JSON N={N} does not match --N {args.N}")
    if args.n is not None and args.n != n:
        raise SystemExit(f"JSON n={n} does not match --n {args.n}")

    missing = 0
    for a in range(N):
        for b in range(N):
            if b == a:
                continue
            for c in range(N):
                if c == a or c == b:
                    continue
                if (a, b, c) not in sigma:
                    missing += 1
    if missing:
        raise SystemExit(f"missing {missing} ordered triples in sigma")

    # swap12
    swap_violation = None
    for i in range(N):
        for j in range(N):
            if j == i:
                continue
            for k in range(N):
                if k == i or k == j:
                    continue
                if sigma[(i, j, k)] != (not sigma[(j, i, k)]):
                    swap_violation = (i, j, k)
                    break
            if swap_violation:
                break
        if swap_violation:
            break

    # cycle
    cycle_violation = None
    for i in range(N):
        for j in range(N):
            if j == i:
                continue
            for k in range(N):
                if k == i or k == j:
                    continue
                if sigma[(i, j, k)] != sigma[(j, k, i)]:
                    cycle_violation = (i, j, k)
                    break
            if cycle_violation:
                break
        if cycle_violation:
            break

    # GPRel
    gp_violation = None
    for a in range(N):
        for b in range(N):
            if b == a:
                continue
            for c in range(N):
                if c == a or c == b:
                    continue
                for d in range(N):
                    if d in (a, b, c):
                        continue
                    for e in range(N):
                        if e in (a, b, c, d):
                            continue
                        p1 = (sigma[(a, b, c)] == sigma[(a, d, e)])
                        p2 = not (sigma[(a, b, d)] == sigma[(a, c, e)])
                        p3 = (sigma[(a, b, e)] == sigma[(a, c, d)])
                        if p1 == p2 == p3:
                            gp_violation = (a, b, c, d, e)
                            break
                    if gp_violation:
                        break
                if gp_violation:
                    break
            if gp_violation:
                break
        if gp_violation:
            break

    # Acyclic
    acyclic_violation = None
    for a in range(N):
        for b in range(N):
            if b == a:
                continue
            for c in range(N):
                if c in (a, b):
                    continue
                for d in range(N):
                    if d in (a, b, c):
                        continue
                    if sigma[(a, b, c)] and (not sigma[(d, b, c)]) and (not sigma[(a, d, c)]) and (
                        not sigma[(a, b, d)]
                    ):
                        acyclic_violation = (a, b, c, d)
                        break
                if acyclic_violation:
                    break
            if acyclic_violation:
                break
        if acyclic_violation:
            break

    alt = find_alternating_sequence(N, n, sigma)

    print(f"N={N} n={n}")
    if swap_violation:
        print(f"swap12 violation at {swap_violation}")
    else:
        print("swap12: OK")
    if cycle_violation:
        print(f"cycle violation at {cycle_violation}")
    else:
        print("cycle: OK")
    if gp_violation:
        print(f"GPRel violation at {gp_violation}")
    else:
        print("GPRel: OK")
    if acyclic_violation:
        print(f"acyclic violation at {acyclic_violation}")
    else:
        print("acyclic: OK")
    if alt is None:
        print("alternating n-sequence: NONE found")
    else:
        print(f"alternating n-sequence: {alt}")


if __name__ == "__main__":
    main()
