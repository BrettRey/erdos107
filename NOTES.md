# Notes

## 2026-01-12

- Lazy SAT run (acyclic, order-blocking, batch=1) for n=6, N=16:
  - Command: `python3 scripts/encode_om3.py --n 6 --N 16 --acyclic --lazy --out lazy_6_16.cnf --max-iters 200`
  - Result: reached max-iters with 200 blocked orders; no UNSAT and no counterexample.
- Fixed backtracking to allow empty future candidate set on final step; added sigma dump + verifier.
- Lazy SAT run (acyclic, batch=200) for n=6, N=16:
  - Command: `PYTHONUNBUFFERED=1 python3 scripts/encode_om3.py --n 6 --N 16 --acyclic --lazy --batch 200 --out lazy_6_16.cnf --max-iters 50 --dump-sigma sigma_6_16.json`
  - Result: candidate found; verified by `python3 scripts/verify_no_alternating.py --model sigma_6_16.json`
- Lazy SAT run (acyclic, batch=2000, order-blocking) for n=6, N=17:
  - Command: `PYTHONUNBUFFERED=1 python3 scripts/encode_om3.py --n 6 --N 17 --acyclic --lazy --batch 2000 --out lazy_6_17.cnf --max-iters 50`
  - Result: reached max-iters; total sets seen=7255 / 12376, no UNSAT or counterexample.
- Lazy SAT run (acyclic, batch=2000, order-blocking) for n=6, N=17 (resume):
  - Command: `PYTHONUNBUFFERED=1 python3 scripts/encode_om3.py --n 6 --N 17 --acyclic --lazy --batch 2000 --out lazy_6_17.cnf --max-iters 80 --state state_6_17.json --save-every 1`
  - Result: reached max-iters; total sets seen=8216 / 12376 (iter 80).
  - Resume: `--resume --max-iters 80 --dump-sigma sigma_6_17.json`
  - Result: reached max-iters; total sets seen=10152 / 12376 (iter 160), newly seen sets=14 at iter 160.
- Fully saturated missing 6-sets (state_6_17_fully_saturated.json), solved CNF as SAT but verifier found alternating 6-subset:
  - Witness: subset (0,1,2,4,9,16), order (0,4,1,9,16,2).

## 2026-01-13

- Added witness batching to `scripts/cegis_sat_loop.py` (`--witness-batch`), so each SAT model can saturate multiple witness 6-sets per iteration.
- Overnight CEGIS run (n=6, N=17) continued; no UNSAT or verified counterexample yet.
  - Current work state: `state_6_17_work.json`
  - Log: `logs/cegis_6_17.log`
  - Run command: `python3 scripts/cegis_sat_loop.py --state state_6_17_work.json --out-state state_6_17_work.json --steps 100000 --witness-batch 100`
