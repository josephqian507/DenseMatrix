---
name: provable-computation-demo-benchmark
description: Use when changing executable linear algebra code or performance-sensitive behavior in this repository. Run and interpret `Demos.lean`, compare outputs and timings for `reducedRowEchelonForm`, `LUFactorization`, `LUDet`, and `gaussDet`, and keep benchmark-oriented checks close to the affected module.
---

# Provable Computation Demo And Benchmark Workflow

This skill is for executable validation in `provable_computation`.

## What to validate

- row-operation behavior in `Rref.lean`
- reconstruction behavior for `LUFactorization`
- determinant agreement among `LUDet`, `gaussDet`, and `Matrix.det` where feasible
- timing regressions visible in `Demos.lean`

## Standard commands

- `lake env lean ProvableComputation/linear_algebra/Demos.lean`
- `lake env lean ProvableComputation/linear_algebra/<Target>.lean`
- `lake build`

## Demos-specific guidance

- Reuse the existing sample matrices before inventing new ad hoc examples.
- The 10x10 built-in `Matrix.det` checks are intentionally commented because they overflow/are too expensive; do not "fix" that casually.
- For LU changes, verify both the raw factorization output and `reconstructLU`.
- If you add a new `#eval` or `#time`, keep it small and directly tied to the changed behavior.

## Reporting

- Call out changed outputs, not just pass/fail.
- Call out timing shifts only when they are material or clearly directional.
- If a behavior change is intentional, note which matrices now differ and why.
