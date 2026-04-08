---
name: provable-computation-module-routing
description: Use when deciding where code, proofs, theorems, demos, or exports should live in this repository. Helps route changes among algorithm modules, proof modules, user-facing theorem wrappers, the root export file, and `Demos.lean` without mixing responsibilities.
---

# Provable Computation Module Routing

Use this skill when the user asks where a change belongs, how to organize a refactor, or which file should own a theorem.

## Routing rules

- Put executable matrix algorithms in `Rref.lean`, `LUFactorization.lean`, or `Determinant.lean`.
- Put proof infrastructure in the proof-focused files next to those algorithms.
- Keep `LU_proofs.lean` as the public wrapper layer for LU theorems.
- Keep `ProvableComputation.lean` as the root re-export surface.
- Keep `Demos.lean` for examples, `#eval`, and `#time`; do not make other files depend on it.

## Current repository boundaries

- RREF algorithm: `Rref.lean`
- Echelon and RREF proofs: `EchelonCommonProofs.lean`, `IsInReducedEchelonFormProofs.lean`, `rref_proofs.lean`, `RrefUniqueness.lean`
- LU executable construction: `LUFactorization.lean`
- LU correctness proofs: `LUFactorizationProofs.lean`
- Determinant executable code: `Determinant.lean`
- Determinant proofs: `determinant_proofs.lean` is the natural landing zone for future proof work

## Naming and surface-area guidance

- Follow existing repository vocabulary such as `reducedRowEchelonForm`, `RowEquivalent`, and `IsUnitLowerTriangular`.
- Prefer adding a small theorem to the most local file that owns its concept, then re-export only if it is part of the public surface.
- Avoid hiding real logic in the root file; keep the root file import-only unless there is a strong reason otherwise.
