#!/usr/bin/env python3
from __future__ import annotations

import argparse
import os
import shutil
import time


def tail_lines(path: str, n: int) -> list[str]:
    with open(path, "rb") as f:
        f.seek(0, os.SEEK_END)
        end = f.tell()
        size = min(1024 * 1024, end)
        f.seek(-size, os.SEEK_END)
        data = f.read().splitlines()
    return [line.decode("utf-8", errors="ignore") for line in data[-n:]]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--log", required=True, help="Path to encode_om3 log")
    ap.add_argument("--state", required=True, help="Path to state JSON")
    ap.add_argument("--cnf", required=True, help="Path to CNF file")
    ap.add_argument("--sigma", default="", help="Optional sigma JSON path")
    ap.add_argument("--out-dir", default="artifacts", help="Base output directory")
    ap.add_argument("--name", default="run_6_17_acyclic", help="Prefix for output folder")
    ap.add_argument("--tail", type=int, default=200, help="Number of log lines to capture")
    args = ap.parse_args()

    ts = time.strftime("%Y%m%d_%H%M%S")
    out_dir = os.path.join(args.out_dir, f"{args.name}_{ts}")
    os.makedirs(out_dir, exist_ok=True)

    shutil.copy2(args.log, os.path.join(out_dir, os.path.basename(args.log)))
    shutil.copy2(args.state, os.path.join(out_dir, os.path.basename(args.state)))
    shutil.copy2(args.cnf, os.path.join(out_dir, os.path.basename(args.cnf)))
    if args.sigma and os.path.exists(args.sigma):
        shutil.copy2(args.sigma, os.path.join(out_dir, os.path.basename(args.sigma)))

    tail_path = os.path.join(out_dir, "log_tail.txt")
    lines = tail_lines(args.log, args.tail)
    with open(tail_path, "w", encoding="utf-8") as fp:
        fp.write("\n".join(lines) + "\n")

    print(out_dir)


if __name__ == "__main__":
    main()
