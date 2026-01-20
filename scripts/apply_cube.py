#!/usr/bin/env python3
"""Apply a single cube (list of literals) to a CNF by adding unit clauses."""

from __future__ import annotations

import argparse
from typing import List


def parse_header(lines: List[str]) -> tuple[int, int, int]:
    for idx, line in enumerate(lines):
        if line.startswith("p "):
            parts = line.strip().split()
            if len(parts) >= 4 and parts[1] == "cnf":
                return idx, int(parts[2]), int(parts[3])
    raise SystemExit("No CNF header found")


def read_cube(path: str) -> List[int]:
    with open(path, "r", encoding="utf-8") as fp:
        for line in fp:
            line = line.strip()
            if not line or line.startswith("c") or line.startswith("p"):
                continue
            toks = [int(x) for x in line.split() if x not in {"0"}]
            if toks:
                return toks
    raise SystemExit("No cube literals found")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--cnf", required=True, help="Input CNF file")
    ap.add_argument("--cube", required=True, help="Cube file (one line of literals)")
    ap.add_argument("--out", required=True, help="Output CNF file")
    args = ap.parse_args()

    with open(args.cnf, "r", encoding="utf-8") as fp:
        lines = fp.readlines()

    header_idx, num_vars, num_clauses = parse_header(lines)
    cube = read_cube(args.cube)

    # Collect clause lines (skip comments + header)
    clauses: List[str] = []
    for line in lines:
        if line.startswith("c") or line.startswith("p"):
            continue
        line = line.strip()
        if line:
            clauses.append(line)

    new_count = num_clauses + len(cube)

    with open(args.out, "w", encoding="utf-8") as fp:
        fp.write(f"p cnf {num_vars} {new_count}\n")
        for cl in clauses:
            fp.write(cl + "\n")
        for lit in cube:
            fp.write(f"{lit} 0\n")


if __name__ == "__main__":
    main()
