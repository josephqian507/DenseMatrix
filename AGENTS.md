# Agent Instructions

## Repo Shape

- This is a Lean 4/Lake project pinned by `lean-toolchain` to `leanprover/lean4:v4.33.0`.
- The public library surface is `ProvableComputation.lean`.
- Executable linear algebra code lives under `ProvableComputation/LinearAlgebra/`.
- Examples and benchmark harnesses live under `ProvableComputation/Examples/` and `ProvableComputation/Bench/`.

## Working Rules

- Use Lean LSP diagnostics and proof goals first for proof work.
- Work on one Lean module at a time. While editing it, use the Lean LSP MCP for
  diagnostics, outlines, hover information, goals, and local declaration search.
- Before switching editing focus to another Lean module, run `lake build` from the repository
  root. This refreshes the compiled artifacts that the LSP needs to see changes in the module
  just completed. If it fails, distinguish errors in the module just edited from known blockers
  elsewhere before proceeding.
- After the build, query LSP diagnostics for the next file before changing it. If the LSP reports
  `partial` or `still_elaborating`, wait and poll instead of treating the response as an error.
- Keep builds purposeful: use LSP and narrow checks during work on the current module, and use
  the scoped default `lake build` only for the cross-module handoff described above.
- Keep executable algorithms, correctness proofs, demos, and benchmarks in their owning modules.
- Preserve the project style from `lakefile.toml`: explicit imports and variables, `autoImplicit = false`, and mathlib linting.
- Do not add demo or benchmark code to the public import surface unless the public API intentionally changes.

## Verification

- Narrow Lean check: `lake env lean <path>`.
- Public library check: `lake build`.
- Internal test check: `lake test`.
- Executable benchmark smoke check: `lake exe densematrix_bench --profile smoke --jsonl`.

## Agent skills

### Issue tracker

Issues and PRDs are tracked in GitHub Issues for `uw-math-ai/provable_computation`. See `docs/agents/issue-tracker.md`.

### Triage labels

The repo uses the canonical five-label triage vocabulary. See `docs/agents/triage-labels.md`.

### Domain docs

Single-context layout; read root domain docs if they exist, and otherwise proceed silently. See `docs/agents/domain.md`.
