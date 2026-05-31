/-
Copyright (c) 2026 Provable Computation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Provable Computation contributors
-/

import ProvableComputation.Bench.DenseMatrixBench

/-!
# DenseMatrix benchmark executable

Lake target root for compiled DenseMatrix benchmarks.
-/

open DenseMatrixBench

/--
Executable entry point for the DenseMatrix benchmark Lake target.

Argument parsing and output formatting live in `DenseMatrixBench` so this file
stays a thin target root: it validates CLI flags, prints help when requested,
and otherwise runs the configured JSONL suite.
-/
def main (args : List String) : IO Unit := do
  match parseArgs args with
  | .error err =>
      IO.eprintln err
      IO.eprintln usage
      IO.Process.exit 2
  | .ok cfg =>
      if cfg.showHelp then
        IO.println usage
      else
        writeOutput cfg (← runBenchmarks cfg)
