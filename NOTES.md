# Notes

## 2026-01-12

- Lazy SAT run (acyclic, order-blocking, batch=1) for n=6, N=16:
  - Command: `python3 scripts/encode_om3.py --n 6 --N 16 --acyclic --lazy --out lazy_6_16.cnf --max-iters 200`
  - Result: reached max-iters with 200 blocked orders; no UNSAT and no counterexample.
- Fixed backtracking to allow empty future candidate set on final step; added sigma dump + verifier.
- Lazy SAT run (acyclic, batch=200) for n=6, N=16:
  - Command: `PYTHONUNBUFFERED=1 python3 scripts/encode_om3.py --n 6 --N 16 --acyclic --lazy --batch 200 --out lazy_6_16.cnf --max-iters 50 --dump-sigma sigma_6_16.json`
  - Result: candidate found; verified by `python3 scripts/verify_no_alternating.py --model sigma_6_16.json`
