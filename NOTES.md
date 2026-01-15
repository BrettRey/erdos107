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
- Lean pivot: added `OrderType.Acyclic`, `SATSpec`, and a CNF-spec stub (`SATCNF.satSpecCNF`) with a soundness lemma stub.
- CNF spec now has explicit literals (`Lit.pos` / `Lit.neg`) to support negated clauses.
- Added `SATCNF.valuationOfOrderType` for mapping order types to CNF valuations (soundness stub still TODO).
- Added clause generators for swap/cycle/acyclic to `SATCNF.satSpecCNF` (GPRel/avoidance still TODO).
- Added GPRel clause generator with auxiliary variables (`gp1/gp2/gp3`) and XNOR gadgets; satSpecCNF now includes GPRel.
- Avoidance clauses are now parameterized: `satSpecCNF` takes a list of blocked orders (`Fin n ↪ Fin N`) and adds one clause per order.
- Added `avoidClause_sound` lemma stub (avoids alternating ⇒ each blocked clause is satisfied under valuationOfOrderType).
- Added soundness lemma stubs for swap/cycle/acyclic/GPRel clause families and wired `satSpecCNF_sound` to use a valuation witness.
- Added helper lemmas for clause evaluation (`evalClause_two`, `evalClause_four`, `evalCNF_cons`).
- Added `evalCNF_append` helper (currently stubbed).
- Proved swap/cycle clause soundness (lemmas now discharged); remaining soundness lemmas still stubbed.
- Proved acyclic clause soundness (both single-clause and clause-family).
- Decision log:
  - Keep CEGIS running in the background (no restart).
  - Pivot Lean spec: `satSpecCNF` is parameterized by a blocked-order list (CEGIS-friendly CNF).
  - Proceed with SATCNF proof scaffolding (stubs first, then discharge swap/cycle/acyclic/avoid/GPRel).
- Added `avoidClause_false_iff` lemma and moved `valuationOfOrderType` earlier so avoidance proofs can use it.
- Added `mem_triples_of_lt` lemma to connect `i<j<k` with membership in `triples n`.
- Added `xnorClauses_sound` lemma (valuation satisfies XNOR gadget) to support GPRel soundness proof.
- Updated `scripts/cegis_sat_loop.py` to skip fully saturated n-sets when searching for witnesses.
- Added `.gitignore` patterns for generated CNF/model/state/log artifacts.
- Verified `lake build Erdos107.SATCNF` passes (warnings only) after the new lemma.
- Restarted the long CEGIS run with the updated script (skip saturated sets), writing to `logs/cegis_6_17.log`.
- Pivoted away from long full-saturation solves after >16h runtime; stopped the non-plain CaDiCaL run and parked the compute pipeline to focus on Lean proofs (avoidClause/GPRel/satSpec soundness).
