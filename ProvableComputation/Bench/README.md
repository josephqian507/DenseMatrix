# DenseMatrix benchmarks

The `densematrix_bench` executable is a fixed benchmark suite for DenseMatrix and
Matrix operations. It is not part of the public import surface.

Run the executable smoke check with:

```sh
lake build densematrix_bench
lake exe densematrix_bench --profile smoke --jsonl
```

The Python runner generates a complete, self-describing artifact directory from a
clean checkout. It requires Python 3.10 or later. It records the subject commit/tree
and SHA-256 hashes of the Lean benchmark source and runner; it does not require the
same timing measurements on different machines.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 scripts/run_densematrix_bench.py \
  --profile full \
  --output /path/to/empty-results-directory
```

The runner refuses a dirty source tree and a nonempty output directory. Use
`--overwrite` only to intentionally replace an existing result directory. Pass
`--plots` only where matplotlib or the macOS `sips` converter is available.

The canonical generated layout is:

```text
compiled/     JSONL samples and CSV summary
diagnostics/  environment, build logs, validation, and compiler-IR record
reduce/       exploratory #reduce inputs and summaries
figures/      optional PNG figures
README.md     source and protocol provenance
```
