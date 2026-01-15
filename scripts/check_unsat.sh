#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 3 ]]; then
  echo "usage: $0 <n> <N> <out.cnf> [proof.lrat] [map.txt]" >&2
  exit 1
fi

NVAL="$2"
CNF="$3"
PROOF="${4:-${CNF%.cnf}.lrat}"
MAP="${5:-${CNF%.cnf}.map.txt}"

if ! command -v cadical >/dev/null 2>&1; then
  echo "cadical not found in PATH" >&2
  exit 1
fi

if ! command -v cake_lpr >/dev/null 2>&1; then
  echo "cake_lpr not found in PATH (install it to verify LRAT proofs)" >&2
  exit 1
fi

lake exe emit_cnf "$1" "$NVAL" "$CNF" "$MAP"

cadical --lrat=1 --no-binary "$CNF" "$PROOF"
cake_lpr "$CNF" "$PROOF"

echo "UNSAT proof verified: $PROOF"
