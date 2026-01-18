# Signotope + Canonical Position Encoding Plan

Goal: replace full OM3 + blocked cyclic orders with a smaller SAT encoding.

## A. Canonical position symmetry breaking
- Fix x-order by index: i < j means x_i < x_j.
- Force point 1 to be extremal.
- Fix radial order around point 1: for all 2 <= i < j <= N, set o(1,i,j)=True.
- Optional mirror kill: fix one extra orientation, e.g. o(2,3,4)=True.

## B. Signotope axioms (4-point forbidden patterns)
- Variables: o(i,j,k) for all i<j<k.
- For each a<b<c<d, forbid alternating patterns on
  (a,b,c), (a,b,d), (a,c,d), (b,c,d):
  - forbid (+ - + -)
  - forbid (- + - +)
  (encode as 2 clauses per 4-tuple).

## C. No-6-gon via Caratheodory / triangulation
Option C1 (inside-triangle variables):
- Introduce in(p; a,b,c) meaning p is inside triangle (a,b,c).
- Use compact clauses to define in() in x-sorted setting.
- For each 6-set S, add clause: OR over p in S of in(p; x1, a, b),
  where x1 is leftmost of S\{p} and (a,b) range over S\{p,x1}.

Option C2 (4-set convexity witness):
- For each 4-set T, introduce nonconvex(T) and define it using
  inside-triangle witnesses.
- For each 6-set S, add clause: OR over 4-subsets T of S of nonconvex(T).

## D. Proof pipeline
- Keep CNF small and streaming-check LRAT via FIFO + cake_lpr.
- If proofs are still large, partition with cube-and-conquer.

## Next steps
1. Prototype encoder in scripts/encode_signotope.py (CLI similar to encode_om3.py).
2. Generate CNF for N=17, n=6 with canonical position enabled.
3. Compare solver time/proof size vs OM3 encoding.
