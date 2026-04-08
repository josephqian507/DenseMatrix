# Provable Computation (Lean 4)

Provable Computation is a Lean 4 library for executable and certifiable algorithms, with a focus on a Gaussian elimination algorithm and a proof of its correctness. Additional linear algebra algorithms are built on top of this framework.

## Team

- Mentor: Dhruv Bhatia
- Members: Alan Chang, Annis Wu, Joseph Qian, Junye Ji, Veer Shukla,
  Zeyin (Michael) Feng

## What is implemented today

- Gaussian elimination algorithm: [`Rref.lean`](./ProvableComputation/linear_algebra/Rref.lean)
- Proofs about echelon forms and Gaussian elimination algorithm:
  - [`EchelonCommonProofs.lean`](./ProvableComputation/linear_algebra/EchelonCommonProofs.lean)
  - [`IsInReducedEchelonFormProofs.lean`](./ProvableComputation/linear_algebra/IsInReducedEchelonFormProofs.lean)
  - [`rref_proofs.lean`](./ProvableComputation/linear_algebra/rref_proofs.lean)
  - [`RrefUniqueness.lean`](./ProvableComputation/linear_algebra/RrefUniqueness.lean)
- LU factorization and determinant computation modules (work in progress):
  - [`LUFactorization.lean`](./ProvableComputation/linear_algebra/LUFactorization.lean)
  - [`Determinant.lean`](./ProvableComputation/linear_algebra/Determinant.lean)
- Test file
  - [`Demos.lean`](./ProvableComputation/linear_algebra/Demos.lean)

## Toolchain

- Lean toolchain: `leanprover/lean4:v4.29.0-rc8` (from [`lean-toolchain`](./lean-toolchain))
- Build tool: Lake
- This project is pinned to the latest official `mathlib4` tag available on the Lean 4.29 line.

## Quick start

```bash
lake build
```

## Current boundaries

- [`LUFactorization.lean`](./ProvableComputation/linear_algebra/LUFactorization.lean)
  contains the LU construction and shared internal helpers.
- [`LUFactorizationProofs.lean`](./ProvableComputation/linear_algebra/LUFactorizationProofs.lean)
  contains the main LU correctness proofs.
- [`LU_proofs.lean`](./ProvableComputation/linear_algebra/LU_proofs.lean)
  re-exports the user-facing LU theorems.
- [`determinant_proofs.lean`](./ProvableComputation/linear_algebra/determinant_proofs.lean)
  is currently empty.

## Poster

![Poster from UW Math AI Poster Session (03/16/2026)](./postersession_3-16-2026.png)

## TODO

1. Add determinant proof in `determinant_proofs.lean`.
