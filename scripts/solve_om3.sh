#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: solve_om3.sh [options]

Encodes OM3 CNF with encode_om3.py, runs CaDiCaL with LRAT output, and:
  - on UNSAT: verifies the LRAT proof with cake_lpr
  - on SAT: extracts a full model, decodes sigma, and verifies no alternating subset

Options:
  --n <n>            Alternating subset size (default: 6)
  --N <N>            Number of points (default: 17)
  --state <file>     Resume state for blocked orders (required for lazy max-iters=0)
  --out <file>       CNF output path (default: /tmp/om3_<n>_<N>.cnf)
  --map <file>       Map output path (default: <out>.map.json)
  --proof <file>     LRAT proof output (default: <out>.lrat)
  --model <file>     SAT model output (default: <out>.out)
  --sigma <file>     Decoded sigma JSON (default: <out>.sigma.json)
  --no-acyclic       Disable acyclic constraints
  --no-lazy          Disable lazy mode (encode full avoidance clauses)
  --max-iters <k>    encode_om3 lazy iterations (default: 0)
  --batch <k>        encode_om3 lazy batch size (default: 0)
  --block-set        encode_om3 block all orders per witness set
  --no-resume        Do not resume from state (still passes --state)
  -h, --help         Show this help
USAGE
}

n=6
N=17
STATE=""
OUT=""
MAP=""
PROOF=""
MODEL=""
SIGMA=""
ACYCLIC=1
LAZY=1
MAX_ITERS=0
BATCH=0
BLOCK_SET=0
RESUME=1

while [[ $# -gt 0 ]]; do
  case "$1" in
    --n) n="$2"; shift 2 ;;
    --N) N="$2"; shift 2 ;;
    --state) STATE="$2"; shift 2 ;;
    --out) OUT="$2"; shift 2 ;;
    --map) MAP="$2"; shift 2 ;;
    --proof) PROOF="$2"; shift 2 ;;
    --model) MODEL="$2"; shift 2 ;;
    --sigma) SIGMA="$2"; shift 2 ;;
    --no-acyclic) ACYCLIC=0; shift ;;
    --no-lazy) LAZY=0; shift ;;
    --max-iters) MAX_ITERS="$2"; shift 2 ;;
    --batch) BATCH="$2"; shift 2 ;;
    --block-set) BLOCK_SET=1; shift ;;
    --no-resume) RESUME=0; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "Unknown argument: $1" >&2; usage; exit 1 ;;
  esac
done

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ENCODER="$ROOT_DIR/scripts/encode_om3.py"
DECODE="$ROOT_DIR/scripts/decode_model.py"
VERIFY="$ROOT_DIR/scripts/verify_no_alternating.py"

if [[ -n "$STATE" && ! -f "$STATE" && -f "$ROOT_DIR/$STATE" ]]; then
  STATE="$ROOT_DIR/$STATE"
fi

if [[ -z "$OUT" ]]; then
  OUT="/tmp/om3_${n}_${N}.cnf"
fi
if [[ -z "$MAP" ]]; then
  MAP="${OUT%.cnf}.map.json"
fi
if [[ -z "$PROOF" ]]; then
  PROOF="${OUT%.cnf}.lrat"
fi
if [[ -z "$MODEL" ]]; then
  MODEL="${OUT%.cnf}.out"
fi
if [[ -z "$SIGMA" ]]; then
  SIGMA="${OUT%.cnf}.sigma.json"
fi

if ! command -v python3 >/dev/null 2>&1; then
  echo "python3 not found in PATH" >&2
  exit 1
fi
if ! command -v cadical >/dev/null 2>&1; then
  echo "cadical not found in PATH" >&2
  exit 1
fi

if [[ "$LAZY" -eq 1 && "$MAX_ITERS" -eq 0 && -z "$STATE" ]]; then
  echo "error: --lazy with --max-iters 0 requires --state to include blocked orders." >&2
  exit 1
fi

mkdir -p "$(dirname "$OUT")"

cmd=(python3 "$ENCODER" --n "$n" --N "$N" --out "$OUT" --map-out "$MAP")
if [[ "$ACYCLIC" -eq 1 ]]; then
  cmd+=(--acyclic)
fi
if [[ "$LAZY" -eq 1 ]]; then
  cmd+=(--lazy --max-iters "$MAX_ITERS")
  if [[ "$BATCH" -ne 0 ]]; then
    cmd+=(--batch "$BATCH")
  fi
fi
if [[ -n "$STATE" ]]; then
  cmd+=(--state "$STATE")
  if [[ "$RESUME" -eq 1 ]]; then
    cmd+=(--resume)
  fi
fi
if [[ "$BLOCK_SET" -eq 1 ]]; then
  cmd+=(--block-set)
fi

echo "Encoding CNF..."
"${cmd[@]}"

if [[ "$n" -eq 6 && "$N" -eq 17 ]]; then
  expected="p cnf 96900 1982201"
  hdr="$(grep -m1 -E '^p[[:space:]]+cnf[[:space:]]+' "$OUT" || true)"
  echo "CNF header: $hdr"
  echo "CNF sha256: $(shasum -a 256 "$OUT" | awk '{print $1}')"
  echo "CNF bytes:  $(wc -c <"$OUT")"
  if [[ "$hdr" != "$expected" ]]; then
    echo "ERROR: unexpected CNF header (expected: '$expected')" >&2
    exit 2
  fi
fi

echo "Running CaDiCaL (LRAT)..."
set +e
cadical --lrat=1 --no-binary "$OUT" "$PROOF"
rc=$?
set -e

if [[ $rc -eq 20 ]]; then
  echo "cadical: UNSAT"
  if ! command -v cake_lpr >/dev/null 2>&1; then
    echo "cake_lpr not found in PATH (install it to verify LRAT proofs)" >&2
    exit 1
  fi
  cake_lpr "$OUT" "$PROOF"
  echo "UNSAT proof verified: $PROOF"
  exit 0
elif [[ $rc -eq 10 ]]; then
  echo "cadical: SAT"
  cadical -q --plain "$OUT" > "$MODEL"
  python3 "$DECODE" --map "$MAP" --model "$MODEL" --n "$n" --N "$N" --out "$SIGMA"
  python3 "$VERIFY" --model "$SIGMA"
  echo "SAT model verified: $SIGMA"
  exit 0
else
  echo "cadical exited with code $rc" >&2
  exit $rc
fi
