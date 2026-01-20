# Cube-and-Conquer Plan (CaDiCaL inccnf)

This repo includes `scripts/cube_inccnf.py` to generate `p inccnf` files
with cubes appended as `a ... 0` lines, which CaDiCaL supports.

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

## Notes

- For large K, use `--max-cubes` to sample a subset.
- `--var-list` lets you choose specific split variables.
- For proof logging per cube, run CaDiCaL on each cube separately with LRAT.
