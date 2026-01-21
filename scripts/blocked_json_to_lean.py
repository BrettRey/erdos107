#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from typing import List


def canonical_rotate_min(seq: List[int]) -> List[int]:
    if not seq:
        return seq
    m = min(seq)
    i = seq.index(m)
    return seq[i:] + seq[:i]


def lean_embedding(order: List[int], n: int, N: int) -> str:
    vals = ", ".join(f"⟨{v}, by decide⟩" for v in order)
    return (
        "(by\n"
        "    classical\n"
        f"    let vals : List (Fin {N}) := [{vals}]\n"
        "    have hnodup : vals.Nodup := by decide\n"
        "    refine ⟨(fun i => vals.get ⟨i.1, by simpa [vals] using i.isLt⟩), ?_⟩\n"
        "    intro i j h\n"
        "    apply Fin.ext\n"
        "    have h' :\n"
        "      vals.get ⟨i.1, by simpa [vals] using i.isLt⟩ =\n"
        "      vals.get ⟨j.1, by simpa [vals] using j.isLt⟩ := by\n"
        "        simpa using h\n"
        "    have hidx :\n"
        "      (⟨i.1, by simpa [vals] using i.isLt⟩ : Fin vals.length) =\n"
        "      ⟨j.1, by simpa [vals] using j.isLt⟩ := (List.Nodup.get_inj_iff hnodup).1 h'\n"
        "    simpa using congrArg Fin.val hidx\n"
        "  )"
    )


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", required=True, help="Path to JSON state file")
    ap.add_argument("--out", required=True, help="Lean output path")
    ap.add_argument("--n", type=int, required=True, help="n (subset size)")
    ap.add_argument("--N", type=int, required=True, help="N (ground set size)")
    ap.add_argument("--name", required=True, help="Lean definition name")
    args = ap.parse_args()

    with open(args.json, "r", encoding="utf-8") as fp:
        data = json.load(fp)

    if "blocked_orders" not in data:
        raise SystemExit("JSON missing 'blocked_orders'")

    if "N" in data and int(data["N"]) != args.N:
        raise SystemExit(f"JSON N={data['N']} does not match --N {args.N}")
    if "n" in data and int(data["n"]) != args.n:
        raise SystemExit(f"JSON n={data['n']} does not match --n {args.n}")

    blocked = data["blocked_orders"]
    if not isinstance(blocked, list):
        raise SystemExit("'blocked_orders' must be a list")

    orders: List[List[int]] = []
    for idx, order in enumerate(blocked):
        if not isinstance(order, list):
            raise SystemExit(f"blocked_orders[{idx}] is not a list")
        if len(order) != args.n:
            raise SystemExit(f"blocked_orders[{idx}] has length {len(order)} (expected {args.n})")
        if len(set(order)) != len(order):
            raise SystemExit(f"blocked_orders[{idx}] has duplicates: {order}")
        if any((v < 0 or v >= args.N) for v in order):
            raise SystemExit(f"blocked_orders[{idx}] has out-of-range vertex: {order}")
        canon = canonical_rotate_min(order)
        orders.append(canon)

    with open(args.out, "w", encoding="utf-8") as fp:
        fp.write("import Mathlib.Data.Fin.Basic\n")
        fp.write("import Mathlib.Data.Fin.Embedding\n")
        fp.write("import Mathlib.Data.List.Nodup\n\n")
        fp.write("namespace ErdosSzekeres\n")
        fp.write("noncomputable section\n")
        fp.write(f"def {args.name} : List (Fin {args.n} ↪ Fin {args.N}) := [\n")
        for i, order in enumerate(orders):
            emb = lean_embedding(order, args.n, args.N)
            sep = "," if i + 1 < len(orders) else ""
            fp.write(f"  {emb}{sep}\n")
        fp.write("]\n")
        fp.write("end\n")
        fp.write("end ErdosSzekeres\n")


if __name__ == "__main__":
    main()
