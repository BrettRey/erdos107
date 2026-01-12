#!/usr/bin/env python3
from __future__ import annotations

import argparse
import itertools
import json
from typing import Dict, Tuple


def load_sigma(path: str) -> Tuple[int, int, Dict[Tuple[int, int, int], bool]]:
    with open(path, "r", encoding="utf-8") as fp:
        obj = json.load(fp)
    N = int(obj["N"])
    n = int(obj["n"])
    sigma_raw = obj["sigma"]
    sigma: Dict[Tuple[int, int, int], bool] = {}
    for k, v in sigma_raw.items():
        a, b, c = (int(x) for x in k.split(","))
        sigma[(a, b, c)] = bool(v)
    return N, n, sigma


def is_alternating_order(sigma: Dict[Tuple[int, int, int], bool], order) -> bool:
    n = len(order)
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                if not sigma[(order[i], order[j], order[k])]:
                    return False
    return True


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--model", required=True)
    args = ap.parse_args()

    N, n, sigma = load_sigma(args.model)

    for subset in itertools.combinations(range(N), n):
        m = min(subset)
        rest = [x for x in subset if x != m]
        for perm in itertools.permutations(rest):
            order = (m,) + perm
            if is_alternating_order(sigma, order):
                print("FOUND alternating subset")
                print("subset:", subset)
                print("order :", order)
                raise SystemExit(1)

    print(f"Verified: no alternating {n}-subset exists in this model.")
    raise SystemExit(0)


if __name__ == "__main__":
    main()
