# Notes

## 2026-01-12

- Lazy SAT run (acyclic, order-blocking) for n=6, N=16:
  - Command: `python3 scripts/encode_om3.py --n 6 --N 16 --acyclic --lazy --out lazy_6_16.cnf --max-iters 200`
  - Result: reached max-iters with 200 blocked orders; no UNSAT and no counterexample.
