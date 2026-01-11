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

## Layout

- `Erdos107/ErdosSzekeres.lean` — geometry + witnesses
- `Erdos107/OrderType.lean` — abstract order types / chirotopes
- `Erdos107/Bridge.lean` — reduction statements (stubs)
- `scripts/encode_om3.py` — SAT encoder for OM3 counterexamples

## Notes

The CNF files generated in the repo are reproducible artifacts; use the script to
regenerate them as needed.
