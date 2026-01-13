#!/usr/bin/env python3
from __future__ import annotations

import argparse
import itertools
import json
import math
import os
import subprocess
import sys
from collections import Counter
from typing import Dict, Iterable, List, Tuple


def run(cmd: List[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, capture_output=True, text=True)


def load_state(path: str) -> dict:
    with open(path, "r", encoding="utf-8") as fp:
        return json.load(fp)


def save_state(path: str, data: dict) -> None:
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as fp:
        json.dump(data, fp)
    os.replace(tmp, path)


def extract_sigma_map(obj: dict) -> Dict[str, int]:
    # Support multiple possible shapes from map files.
    for key in ("sigma_var", "sigma", "sigmaVars", "sigma_vars", "map"):
        if key in obj and isinstance(obj[key], dict):
            obj = obj[key]
            break

    def norm_triple_str(s: str) -> str:
        s = s.strip().strip("()[]{}")
        s = s.replace(" ", "")
        return s

    sample_k = next(iter(obj.keys()))
    sample_v = obj[sample_k]

    triple_to_var: Dict[str, int] = {}
    if isinstance(sample_v, int) and isinstance(sample_k, str):
        for k, v in obj.items():
            triple_to_var[norm_triple_str(k)] = int(v)
    else:
        for k, v in obj.items():
            var = int(k)
            if isinstance(v, (list, tuple)) and len(v) == 3:
                triple_to_var[f"{v[0]},{v[1]},{v[2]}"] = var
            elif isinstance(v, str):
                triple_to_var[norm_triple_str(v)] = var
            else:
                raise SystemExit(f"Unrecognised sigma map entry: {k}: {v!r}")
    return triple_to_var


def parse_model(path: str) -> Dict[int, bool]:
    assign: Dict[int, bool] = {}
    with open(path, "r", encoding="utf-8") as fp:
        for line in fp:
            if not line.startswith("v"):
                continue
            for tok in line.split()[1:]:
                lit = int(tok)
                if lit == 0:
                    continue
                assign[abs(lit)] = (lit > 0)
    return assign


def build_sigma(triple_to_var: Dict[str, int], assign: Dict[int, bool]) -> Dict[Tuple[int, int, int], bool]:
    sigma: Dict[Tuple[int, int, int], bool] = {}
    missing = 0
    for t, var in triple_to_var.items():
        if var not in assign:
            missing += 1
            continue
        a, b, c = (int(x) for x in t.split(","))
        sigma[(a, b, c)] = bool(assign[var])
    if missing:
        raise SystemExit("Model missing sigma variables (did you forget --plain?).")
    return sigma


def saturated_sets_from_blocked(blocked_orders: set[Tuple[int, ...]], n: int) -> set[Tuple[int, ...]]:
    threshold = math.factorial(n - 1)
    counts = Counter(tuple(sorted(o)) for o in blocked_orders)
    return {s for s, k in counts.items() if k >= threshold}


def find_witnesses(
    sigma: Dict[Tuple[int, int, int], bool],
    N: int,
    n: int,
    saturated_sets: set[Tuple[int, ...]],
    limit: int,
) -> List[Tuple[Tuple[int, ...], Tuple[int, ...]]]:
    out: List[Tuple[Tuple[int, ...], Tuple[int, ...]]] = []
    for subset in itertools.combinations(range(N), n):
        if limit and len(out) >= limit:
            break
        if subset in saturated_sets:
            continue
        m = min(subset)
        rest = [x for x in subset if x != m]
        for perm in itertools.permutations(rest):
            order = (m,) + perm
            ok = True
            for i in range(n):
                for j in range(i + 1, n):
                    for k in range(j + 1, n):
                        if not sigma[(order[i], order[j], order[k])]:
                            ok = False
                            break
                    if not ok:
                        break
                if not ok:
                    break
            if ok:
                out.append((subset, order))
                break
    return out


def saturate_subset(blocked_orders: set[Tuple[int, ...]], subset: Iterable[int]) -> int:
    subset = tuple(sorted(subset))
    m = subset[0]
    rest = subset[1:]
    added = 0
    for perm in itertools.permutations(rest):
        order = (m,) + perm
        if order not in blocked_orders:
            blocked_orders.add(order)
            added += 1
    return added


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--state", required=True)
    ap.add_argument("--out-state", required=True)
    ap.add_argument("--n", type=int, default=6)
    ap.add_argument("--N", type=int, default=17)
    ap.add_argument("--steps", type=int, default=1)
    ap.add_argument(
        "--witness-batch",
        type=int,
        default=100,
        help="How many witness n-sets to saturate per SAT model (0 = no limit).",
    )
    ap.add_argument("--cnf", default="fullsat_6_17.cnf")
    ap.add_argument("--map", default="map_6_17.json")
    ap.add_argument("--model-out", default="sat_6_17.out")
    args = ap.parse_args()

    state_path = args.state
    out_path = args.out_state

    for step in range(args.steps):
        # Generate CNF + map for current state
        cmd = [
            "python3",
            "scripts/encode_om3.py",
            "--n",
            str(args.n),
            "--N",
            str(args.N),
            "--acyclic",
            "--lazy",
            "--batch",
            "1",
            "--out",
            args.cnf,
            "--max-iters",
            "0",
            "--state",
            state_path,
            "--resume",
            "--map-out",
            args.map,
        ]
        res = run(cmd)
        if res.returncode != 0:
            sys.stderr.write(res.stdout)
            sys.stderr.write(res.stderr)
            raise SystemExit("encode_om3 failed")

        # Solve CNF
        res = run(["cadical", "-q", "--plain", args.cnf])
        with open(args.model_out, "w", encoding="utf-8") as fp:
            fp.write(res.stdout)
        if res.returncode == 20:
            print("UNSAT")
            return
        if res.returncode != 10:
            raise SystemExit("cadical failed")

        # Build sigma from model
        m = json.load(open(args.map, "r", encoding="utf-8"))
        triple_to_var = extract_sigma_map(m)
        assign = parse_model(args.model_out)
        sigma = build_sigma(triple_to_var, assign)

        data = load_state(state_path)
        blocked = set(tuple(o) for o in data["blocked_orders"])
        saturated_sets = saturated_sets_from_blocked(blocked, args.n)

        # Find witness
        witnesses = find_witnesses(sigma, args.N, args.n, saturated_sets, args.witness_batch)
        if not witnesses:
            print("Verified: no alternating subset exists (counterexample candidate).")
            return

        print(
            f"Found {len(witnesses)} witness set(s); first subset={witnesses[0][0]} order={witnesses[0][1]}"
        )

        # Saturate witness subsets
        total_added = 0
        for subset, _order in witnesses:
            total_added += saturate_subset(blocked, subset)
            saturated_sets.add(tuple(sorted(subset)))
        data["blocked_orders"] = [list(o) for o in blocked]
        data["flags"] = {"acyclic": True, "block_set": False}
        save_state(out_path, data)
        print("Added orders:", total_added, "total blocked orders:", len(blocked))

        # next iteration reads from out_state
        state_path = out_path


if __name__ == "__main__":
    main()
