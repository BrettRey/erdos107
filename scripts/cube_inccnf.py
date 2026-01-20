#!/usr/bin/env python3
"""Generate an incremental CNF (p inccnf) with cubes appended.

Cubes are emitted as lines starting with 'a', each ending with 0.
This matches common inccnf formats supported by CaDiCaL.
"""

from __future__ import annotations

import argparse
import itertools
import random
from typing import Iterable, List


def parse_header(lines: Iterable[str]) -> tuple[int, int]:
    for line in lines:
        if line.startswith("p "):
            parts = line.strip().split()
            if len(parts) >= 4 and parts[1] == "cnf":
                return int(parts[2]), int(parts[3])
    raise SystemExit("No CNF header found")


def gen_all_cubes(var_list: List[int]) -> Iterable[List[int]]:
    for bits in itertools.product([0, 1], repeat=len(var_list)):
        cube = []
        for v, b in zip(var_list, bits):
            cube.append(v if b == 1 else -v)
        yield cube


def gen_random_cubes(var_list: List[int], max_cubes: int, seed: int) -> Iterable[List[int]]:
    rnd = random.Random(seed)
    seen = set()
    while len(seen) < max_cubes:
        bits = tuple(rnd.getrandbits(1) for _ in var_list)
        if bits in seen:
            continue
        seen.add(bits)
        cube = [v if b == 1 else -v for v, b in zip(var_list, bits)]
        yield cube


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--cnf", required=True, help="Input CNF file")
    ap.add_argument("--out", required=True, help="Output inccnf file")
    ap.add_argument("--vars", type=int, default=0, help="Use vars 1..K as split vars")
    ap.add_argument("--var-list", type=str, default="", help="Comma-separated var list")
    ap.add_argument("--max-cubes", type=int, default=0, help="Limit number of cubes (random sampling)")
    ap.add_argument("--seed", type=int, default=0, help="RNG seed for sampling")
    ap.add_argument("--cubes-only", action="store_true", help="Only emit cubes (no CNF)")
    args = ap.parse_args()

    if args.vars <= 0 and not args.var_list:
        raise SystemExit("Provide --vars or --var-list")

    if args.var_list:
        var_list = [int(x) for x in args.var_list.split(",") if x.strip()]
    else:
        var_list = list(range(1, args.vars + 1))

    if args.max_cubes and args.max_cubes > 0:
        cubes = list(gen_random_cubes(var_list, args.max_cubes, args.seed))
    else:
        if len(var_list) > 20:
            raise SystemExit("Refusing to enumerate 2^K cubes for K>20; use --max-cubes")
        cubes = list(gen_all_cubes(var_list))

    if args.cubes_only:
        with open(args.out, "w", encoding="utf-8") as fp:
            for cube in cubes:
                fp.write("a " + " ".join(str(x) for x in cube) + " 0\n")
        return

    with open(args.cnf, "r", encoding="utf-8") as fp:
        lines = fp.readlines()

    num_vars, num_clauses = parse_header(lines)

    with open(args.out, "w", encoding="utf-8") as fp:
        fp.write(f"p inccnf {num_vars} {num_clauses}\n")
        for line in lines:
            if line.startswith("c ") or line.startswith("p "):
                continue
            fp.write(line)
        fp.write("c cubes\n")
        for cube in cubes:
            fp.write("a " + " ".join(str(x) for x in cube) + " 0\n")


if __name__ == "__main__":
    main()
