# Provable Computation (Lean 4)

Provable Computation is a Lean 4 library for executable and certifiable algorithms, with a
focus on Gaussian elimination, LU factorization, and determinant computation.

## Team

- Mentor: Dhruv Bhatia
- Members: Alan Chang, Annis Wu, Joseph Qian, Junye Ji, Veer Shukla,
  Zeyin (Michael) Feng

## Current module tree

- DenseMatrix backend:
  - [`Defs.lean`](./ProvableComputation/LinearAlgebra/DenseMatrix/Defs.lean)
  - [`Elementary.lean`](./ProvableComputation/LinearAlgebra/DenseMatrix/Elementary.lean)
- Core echelon predicates:
  - [`Echelon.lean`](./ProvableComputation/LinearAlgebra/Echelon.lean)
- Gaussian elimination:
  - [`Defs.lean`](./ProvableComputation/LinearAlgebra/GaussianElimination/Defs.lean)
  - [`Rref.lean`](./ProvableComputation/LinearAlgebra/GaussianElimination/Rref.lean)
  - [`Elementary.lean`](./ProvableComputation/LinearAlgebra/GaussianElimination/Elementary.lean)
  - [`Pivot.lean`](./ProvableComputation/LinearAlgebra/GaussianElimination/Pivot.lean)
  - [`RrefCorrectness.lean`](./ProvableComputation/LinearAlgebra/GaussianElimination/RrefCorrectness.lean)
  - [`RrefUniqueness.lean`](./ProvableComputation/LinearAlgebra/GaussianElimination/RrefUniqueness.lean)
- LU factorization:
  - [`Defs.lean`](./ProvableComputation/LinearAlgebra/LU/Defs.lean)
  - [`Basic.lean`](./ProvableComputation/LinearAlgebra/LU/Basic.lean)
  - [`Correctness.lean`](./ProvableComputation/LinearAlgebra/LU/Correctness.lean)
- Determinant:
  - [`Basic.lean`](./ProvableComputation/LinearAlgebra/Determinant/Basic.lean)
  - [`Correctness.lean`](./ProvableComputation/LinearAlgebra/Determinant/Correctness.lean)
- Examples and benchmarks:
  - [`GaussianEliminationDemos.lean`](./ProvableComputation/Examples/GaussianEliminationDemos.lean)
  - [`DenseMatrixBench.lean`](./ProvableComputation/Bench/DenseMatrixBench.lean)
  - [`DenseMatrixKernel.lean`](./ProvableComputation/Bench/DenseMatrixKernel.lean)
  - [`DenseMatrixRunner.lean`](./ProvableComputation/Bench/DenseMatrixRunner.lean)
  - [`DeterminantRuntimeComparator.lean`](./ProvableComputation/Bench/DeterminantRuntimeComparator.lean)

## Toolchain

- Lean toolchain: `leanprover/lean4:v4.30.0` (from [`lean-toolchain`](./lean-toolchain))
- Build tool: Lake
- This project is pinned to `mathlib4` tag `v4.30.0` on the Lean 4.30 line.

## Quick start

```bash
lake exe cache get
lake build
```

## DenseMatrix benchmarks

The DenseMatrix benchmark executable is available as the Lake target
`densematrix_bench`:

```bash
lake build densematrix_bench
lake exe densematrix_bench --quick --jsonl -
```

Use `--jsonl PATH` to write JSONL output to a file, or `--jsonl -` to write it
to stdout.

## Public entrypoints

- `Matrix.rowEchelonForm` and `Matrix.reducedRowEchelonForm`
  return `Matrix.RowReductionResult` with named fields `matrix` and `steps`,
  routed through the native DenseMatrix backend.
- `Matrix.luFactorization`
  returns `Matrix.LUFactors` with named fields `P`, `L`, and `U`, routed
  through the native DenseMatrix backend.
- `Matrix.gaussDet` and `Matrix.luDet`
  expose the determinant algorithms on the namespaced public API.
- `DenseMatrix.rowEchelonForm`, `DenseMatrix.reducedRowEchelonForm`,
  `DenseMatrix.luFactorization`, `DenseMatrix.gaussDet`, and
  `DenseMatrix.luDet` expose the DenseMatrix-facing executable surface.

## Poster

![Poster from UW Math AI Poster Session (03/16/2026)](./postersession_3-16-2026.png)

## Status

- The old `linear_algebra/` tree has been replaced by the `LinearAlgebra/` hierarchy.
- Demo and benchmark code live outside the core library import surface.
- Determinant correctness is proved in `Determinant/Correctness.lean` for the
  public Matrix API and native DenseMatrix backend.
