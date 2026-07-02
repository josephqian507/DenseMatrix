import ProvableComputation.LinearAlgebra.DenseMatrix.Defs

/-!
# DenseMatrix benchmarks

Small executable benchmarks for the DenseMatrix performance comparison points.
-/

namespace DenseMatrixBench

structure BenchConfig where
  smulRows : Nat
  smulCols : Nat
  dotRows : Nat
  dotInner : Nat
  dotCols : Nat
  iterations : Nat
  dotRows_pos : 0 < dotRows
  dotInner_pos : 0 < dotInner
  dotCols_pos : 0 < dotCols

structure BenchResult where
  name : String
  nanos : Nat
  checksum : Nat

def quickConfig : BenchConfig where
  smulRows := 80
  smulCols := 80
  dotRows := 16
  dotInner := 5000
  dotCols := 16
  iterations := 200
  dotRows_pos := by decide
  dotInner_pos := by decide
  dotCols_pos := by decide

def defaultConfig : BenchConfig where
  smulRows := 150
  smulCols := 150
  dotRows := 20
  dotInner := 10000
  dotCols := 20
  iterations := 300
  dotRows_pos := by decide
  dotInner_pos := by decide
  dotCols_pos := by decide

def entryA (i j : Nat) : Nat :=
  (i * 17 + j * 31 + 7) % 97

def entryB (i j : Nat) : Nat :=
  ((i + 3) * 19 + (j + 5) * 23) % 89

def denseA (m n : Nat) : DenseMatrix m n Nat :=
  DenseMatrix.of fun i j => entryA i.val j.val

def denseB (m n : Nat) : DenseMatrix m n Nat :=
  DenseMatrix.of fun i j => entryB i.val j.val

def matrixA (m n : Nat) : Matrix (Fin m) (Fin n) Nat :=
  Matrix.of fun i j => entryA i.val j.val

def denseChecksum {m n : Nat} (M : DenseMatrix m n Nat) : Nat :=
  ∑ i : Fin m, ∑ j : Fin n, M.get i j

def matrixChecksum {m n : Nat} (M : Matrix (Fin m) (Fin n) Nat) : Nat :=
  ∑ i : Fin m, ∑ j : Fin n, M i j

def finMod (n : Nat) (h : 0 < n) (x : Nat) : Fin n :=
  ⟨x % n, Nat.mod_lt x h⟩

def repeatChecksum (iterations : Nat) (run : Nat → Nat) : Nat := Id.run do
  let mut checksum := 0
  for i in [0:iterations] do
    checksum := checksum + run i
  return checksum

def timeNat (name : String) (run : Unit → Nat) : IO BenchResult := do
  let start ← IO.monoNanosNow
  let checksum := run ()
  if checksum == 0 then
    IO.eprintln s!"{name}: zero checksum"
  let stop ← IO.monoNanosNow
  return { name := name, nanos := stop - start, checksum := checksum }

def benchDenseSmul (cfg : BenchConfig) : IO BenchResult := do
  let source := denseA cfg.smulRows cfg.smulCols
  timeNat "dense_smul" fun _ =>
    repeatChecksum cfg.iterations fun i =>
      denseChecksum (DenseMatrix.smul (i + 2) source)

def benchMathlibSmul (cfg : BenchConfig) : IO BenchResult := do
  let source := matrixA cfg.smulRows cfg.smulCols
  timeNat "mathlib_smul" fun _ =>
    repeatChecksum cfg.iterations fun i =>
      matrixChecksum ((i + 2) • source)

def benchRecursiveDot (cfg : BenchConfig) : IO BenchResult := do
  let A := denseA cfg.dotRows cfg.dotInner
  let B := denseB cfg.dotInner cfg.dotCols
  timeNat "recursive_dot" fun _ =>
    repeatChecksum cfg.iterations fun i =>
      DenseMatrix.dot 0
        (finMod cfg.dotRows cfg.dotRows_pos i)
        (finMod cfg.dotCols cfg.dotCols_pos (i * 3 + 1))
        (finMod cfg.dotInner cfg.dotInner_pos 0)
        A
        B

def benchFinsetSumDot (cfg : BenchConfig) : IO BenchResult := do
  let A := denseA cfg.dotRows cfg.dotInner
  let B := denseB cfg.dotInner cfg.dotCols
  timeNat "finset_sum_dot" fun _ =>
    repeatChecksum cfg.iterations fun i =>
      DenseMatrix.sum_dot
        (finMod cfg.dotRows cfg.dotRows_pos i)
        (finMod cfg.dotCols cfg.dotCols_pos (i * 3 + 1))
        A
        B

def runBenchmarks (cfg : BenchConfig) : IO (List BenchResult) := do
  let denseSmul ← benchDenseSmul cfg
  let mathlibSmul ← benchMathlibSmul cfg
  let recursiveDot ← benchRecursiveDot cfg
  let finsetSumDot ← benchFinsetSumDot cfg
  return [denseSmul, mathlibSmul, recursiveDot, finsetSumDot]

def jsonString (value : String) : String :=
  "\"" ++ value ++ "\""

def jsonLine (result : BenchResult) : String :=
  "{" ++ jsonString "name" ++ ":" ++ jsonString result.name ++ "," ++
    jsonString "nanos" ++ ":" ++ toString result.nanos ++ "," ++
    jsonString "checksum" ++ ":" ++ toString result.checksum ++ "}"

def humanLine (result : BenchResult) : String :=
  s!"{result.name}: {result.nanos} ns, checksum={result.checksum}"

def emitResults (jsonl : Bool) (results : List BenchResult) : IO Unit := do
  for result in results do
    IO.println (if jsonl then jsonLine result else humanLine result)

def main (args : List String) : IO Unit := do
  let cfg := if args.contains "--quick" then quickConfig else defaultConfig
  let results ← runBenchmarks cfg
  emitResults (args.contains "--jsonl") results

end DenseMatrixBench

def main (args : List String) : IO Unit :=
  DenseMatrixBench.main args
