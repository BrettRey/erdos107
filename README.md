# erdos107

Lean formalization of Erdős Problem #107 (Erdős–Szekeres conjecture) with a pipeline from geometry
→ order types (chirotopes) → SAT. The project is structured to keep the conceptual reduction
explicit while the geometric proofs are filled in incrementally.

## Status

- Builds with Lean 4.26.0
- Core definitions in `Erdos107/ErdosSzekeres.lean`
- Abstract order-type layer in `Erdos107/OrderType.lean`
- Bridge statements in `Erdos107/Bridge.lean` (currently `sorry`)

## Quick start

```bash
# From repo root
lake build
```

## SAT encoder (small sanity checks)

A minimal DIMACS encoder for the chirotope-level target is provided at
`scripts/encode_om3.py`. Example runs:

```bash
python3 scripts/encode_om3.py --n 4 --N 4 --out om3_4_4.cnf
cadical om3_4_4.cnf

python3 scripts/encode_om3.py --n 4 --N 5 --out om3_4_5.cnf
cadical om3_4_5.cnf
```

## Certified SAT pipeline (Lean CNF + LRAT)

Lean now defines the CNF spec (`Erdos107/SATCNF.lean`) and can emit DIMACS directly.

```bash
# Emit DIMACS from Lean (no blocked orders yet; this is the base SATSpec CNF)
lake exe emit_cnf 6 17 out.cnf out.map.txt
```

To verify UNSAT with a checkable certificate, use the helper script:

```bash
scripts/check_unsat.sh 6 17 out.cnf
```

This requires `cadical` and `cake_lpr` on your PATH. The script writes an LRAT proof
and verifies it with `cake_lpr`.

## Layout

- `Erdos107/ErdosSzekeres.lean` — geometry + witnesses
- `Erdos107/OrderType.lean` — abstract order types / chirotopes
- `Erdos107/Bridge.lean` — reduction statements (stubs)
- `scripts/encode_om3.py` — SAT encoder for OM3 counterexamples
- `Erdos107/EmitCNF.lean` — Lean DIMACS emitter for `satSpecCNF`
- `scripts/check_unsat.sh` — run CaDiCaL + LRAT proof check via `cake_lpr`

## Notes

The CNF files generated in the repo are reproducible artifacts; use the script to
regenerate them as needed.
