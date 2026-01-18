#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from typing import Dict


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


def build_sigma(triple_to_var: Dict[str, int], assign: Dict[int, bool]) -> Dict[str, bool]:
    sigma: Dict[str, bool] = {}
    missing = 0
    for t, var in triple_to_var.items():
        if var not in assign:
            missing += 1
            continue
        sigma[t] = bool(assign[var])
    if missing:
        raise SystemExit("Model missing sigma variables (did you forget --plain?).")
    return sigma


def infer_N(triple_to_var: Dict[str, int]) -> int:
    max_idx = -1
    for t in triple_to_var.keys():
        a, b, c = (int(x) for x in t.split(","))
        max_idx = max(max_idx, a, b, c)
    return max_idx + 1


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--map", required=True)
    ap.add_argument("--model", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--N", type=int, default=0)
    args = ap.parse_args()

    with open(args.map, "r", encoding="utf-8") as fp:
        m = json.load(fp)
    triple_to_var = extract_sigma_map(m)
    assign = parse_model(args.model)
    sigma = build_sigma(triple_to_var, assign)

    N = args.N if args.N > 0 else infer_N(triple_to_var)
    if N <= 0:
        raise SystemExit("Could not infer N from map; pass --N explicitly.")

    data = {"N": N, "n": int(args.n), "sigma": sigma}
    with open(args.out, "w", encoding="utf-8") as fp:
        json.dump(data, fp, indent=2, sort_keys=True)


if __name__ == "__main__":
    main()
