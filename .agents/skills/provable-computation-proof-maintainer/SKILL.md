---
name: provable-computation-proof-maintainer
description: Use when modifying, debugging, or reviewing Lean proofs and theorem statements in this repository, especially around `Rref`, echelon-form proofs, LU factorization, and determinant correctness. Start with Lean LSP diagnostics and file outlines, then route changes to the right proof file instead of editing demos or re-export files first.
---

# Provable Computation Proof Maintainer

This skill is specific to the `provable_computation` Lean repository.

## Module map

- `ProvableComputation/linear_algebra/Rref.lean`: executable row operations and `rowEchelonForm` / `reducedRowEchelonForm`
- `ProvableComputation/linear_algebra/EchelonCommonProofs.lean`, `IsInReducedEchelonFormProofs.lean`, `rref_proofs.lean`, `RrefUniqueness.lean`: RREF and echelon proof work
- `ProvableComputation/linear_algebra/LUFactorization.lean`: executable PLU/LU construction
- `ProvableComputation/linear_algebra/LUFactorizationProofs.lean`: main LU correctness proofs
- `ProvableComputation/linear_algebra/LU_proofs.lean`: thin user-facing theorem wrappers
- `ProvableComputation/linear_algebra/Determinant.lean`: executable determinant routines
- `ProvableComputation/linear_algebra/determinant_proofs.lean`: proof slot; currently mostly empty

## Workflow

1. Use Lean LSP first: diagnostics, outline, hover/goals.
2. Identify whether the request is about executable code, internal proofs, or user-facing wrapper theorems.
3. Edit the implementation/proof file first. Keep `LU_proofs.lean` and similar re-export files thin unless the public API changes.
4. Preserve repository style: explicit imports, explicit variables, `autoImplicit = false`, small proofs over monolithic ones.
5. After nontrivial proof changes, rerun Lean diagnostics and `lake build`.
6. If executable behavior changed, also run `lake env lean ProvableComputation/linear_algebra/Demos.lean`.

## Repo-specific reminders

- `LUFactorization` returns `(P, L, U)` and the public reconstruction theorems state `P * L * U = M`.
- `Demos.lean` is a smoke-test and timing file, not a dependency target.
- If a theorem belongs in the public surface, check whether it should be re-exported from `ProvableComputation.lean`.
