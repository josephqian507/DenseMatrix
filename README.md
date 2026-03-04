# Provable Computation (Lean 4)

Provable Computation is a Lean 4 library for **executable** and **certified** linear
algebra, centered on a row-reduction pipeline that returns both transformed matrices and
machine-checked correctness guarantees.

## Team

- Leader: Dhruv Bhatia
- Members (alphabetical): Alan (AlanC922), Joseph Qian, Junye Ji, veershukla65,
  Zeyin (Michael) Feng

## What is implemented today

- Executable row operations and RREF pipeline: [`Rref.lean`](./ProvableComputation/linear_algebra/Rref.lean)
- Proof stack for invariants and correctness:
  - [`EchelonCommonProofs.lean`](./ProvableComputation/linear_algebra/EchelonCommonProofs.lean)
  - [`IsInReducedEchelonFormProofs.lean`](./ProvableComputation/linear_algebra/IsInReducedEchelonFormProofs.lean)
  - [`rref_proofs.lean`](./ProvableComputation/linear_algebra/rref_proofs.lean)
  - [`RrefUniqueness.lean`](./ProvableComputation/linear_algebra/RrefUniqueness.lean)
- LU and determinant computation modules:
  - [`LUFactorization.lean`](./ProvableComputation/linear_algebra/LUFactorization.lean)
  - [`Determinant.lean`](./ProvableComputation/linear_algebra/Determinant.lean)

## Toolchain

- Lean toolchain: `leanprover/lean4:v4.24.0` (from [`lean-toolchain`](./lean-toolchain))
- Build tool: Lake

## Quick start

```bash
lake build
```

## Demo commands (for presentation)

Run executable demos (matrix transforms, determinant timing, LU samples):

```bash
lake env lean ProvableComputation/linear_algebra/Demos.lean
```

Compile key proof modules directly:

```bash
lake env lean ProvableComputation/linear_algebra/rref_proofs.lean
lake env lean ProvableComputation/linear_algebra/RrefUniqueness.lean
lake env lean ProvableComputation/linear_algebra/LUFactorization.lean
```

## Current boundaries (transparent status)

- [`LU_proofs.lean`](./ProvableComputation/linear_algebra/LU_proofs.lean) is present but
  incomplete.
- [`determinant_proofs.lean`](./ProvableComputation/linear_algebra/determinant_proofs.lean)
  is currently empty.
- The completed end-to-end formal story today is the RREF pipeline and its semantic
  uniqueness theorem.

## Presentation day copy/paste checklist

```bash
lake build
lake env lean ProvableComputation/linear_algebra/rref_proofs.lean
lake env lean ProvableComputation/linear_algebra/RrefUniqueness.lean
lake env lean ProvableComputation/linear_algebra/LUFactorization.lean
lake env lean ProvableComputation/linear_algebra/Demos.lean
```

## Roadmap (near-term)

1. Complete LU correctness proofs in `LU_proofs.lean`.
2. Add determinant proof layer in `determinant_proofs.lean`.
3. Continue reducing linter warnings and expanding executable benchmark cases.
