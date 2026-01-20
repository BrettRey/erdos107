# Cube-and-Conquer Plan (CaDiCaL inccnf)

This repo includes:
- `scripts/cube_inccnf.py` to generate `p inccnf` files with cubes appended.
- `scripts/apply_cube.py` to materialize a single cube as unit clauses.

## Minimal workflow

1. Generate the base CNF (e.g., signotope or OM3):

```
python3 scripts/encode_signotope.py --n 6 --N 17 --canonical --out /tmp/sig_6_17.cnf
```

2. Generate an incremental CNF with cubes:

```
python3 scripts/cube_inccnf.py --cnf /tmp/sig_6_17.cnf --out /tmp/sig_6_17.inccnf --vars 12
```

3. Solve with CaDiCaL:

```
cadical /tmp/sig_6_17.inccnf
```

CaDiCaL will solve each cube in sequence and stop on SAT; UNSAT is reported
only if all cubes are UNSAT.

## Per-cube workflow (robust)

If the local CaDiCaL build rejects `p inccnf`, use per-cube CNFs instead:

```
python3 scripts/cube_inccnf.py --cnf /tmp/sig_6_17.cnf --out /tmp/cubes.icnf --vars 12 --cubes-only
python3 scripts/apply_cube.py --cnf /tmp/sig_6_17.cnf --cube /tmp/cubes.icnf --out /tmp/with_cube.cnf
cadical /tmp/with_cube.cnf
```

Then distribute cube indices and solve in parallel.

## Notes

- For large K, use `--max-cubes` to sample a subset.
- `--var-list` lets you choose specific split variables.
- For proof logging per cube, run CaDiCaL on each cube separately with LRAT.
