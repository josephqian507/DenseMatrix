import ProvableComputation.LinearAlgebra.DenseMatrix.Defs
import ProvableComputation.LinearAlgebra.DenseMatrix.GaussianElimination.Defs
import ProvableComputation.LinearAlgebra.DenseMatrix.GaussianElimination.Rref
import ProvableComputation.LinearAlgebra.GaussianElimination.Defs
import ProvableComputation.LinearAlgebra.GaussianElimination.Rref

/-!
# DenseMatrix performance baseline

This executable is intentionally a fixed benchmark suite rather than a generic benchmark framework.
Every Matrix result is materialized before timing stops; fingerprints run afterwards.
-/

namespace DenseMatrixBench

universe u v

structure BenchSample where
  suite : String
  operation : String
  variantName : String
  implementation : String
  coefficient : String
  pattern : String
  rows : Nat
  inner : Nat
  cols : Nat
  processRun : Nat
  sample : Nat
  batch : Nat
  nanos : Nat
  heartbeats : Nat
  checksum : UInt64

/-- `implementation` refines the five stable `variant` classes without adding a registry. -/
structure BenchMeta where
  suite : String
  operation : String
  variantName : String
  implementation : String
  coefficient : String
  pattern : String
  rows : Nat
  inner : Nat
  cols : Nat
  processRun : Nat
  sample : Nat
  batch : Nat

structure BenchConfig where
  profile : String
  suite : Option String
  seed : Nat
  processRun : Nat
  jsonl : Bool

structure Shape where
  rows : Nat
  inner : Nat
  cols : Nat

structure ReductionOutput where
  data : Array Rat
  steps : Array UInt64

def defaultConfig : BenchConfig :=
  { profile := "full", suite := none, seed := 1729, processRun := 0, jsonl := false }

def recordedSamples (cfg : BenchConfig) : Nat :=
  if cfg.profile == "smoke" then 2 else 7

def warmups (cfg : BenchConfig) : Nat :=
  if cfg.profile == "smoke" then 1 else 2

@[noinline]
def opaquePure {α : Type} (x : α) : IO α :=
  pure x

def mix (state value : UInt64) : UInt64 :=
  state * 1099511628211 + value + 1469598103934665603

def fingerprintArray {α : Type u} [Hashable α] (xs : Array α) : UInt64 :=
  xs.foldl (fun state value => mix state (hash value)) 1469598103934665603

def fingerprintNatArray (xs : Array Nat) : UInt64 :=
  fingerprintArray xs

def fingerprintRatArray (xs : Array Rat) : UInt64 :=
  fingerprintArray xs

def fingerprintUInt64Array (xs : Array UInt64) : UInt64 :=
  fingerprintArray xs

def fingerprintReduction (output : ReductionOutput) : UInt64 :=
  mix (fingerprintRatArray output.data) (fingerprintUInt64Array output.steps)

def materializeMatrix {m n : Nat} {α : Type} (M : Matrix (Fin m) (Fin n) α) : Array α :=
  Id.run do
    let mut out := Array.mkEmpty (m * n)
    let mut i := 0
    while hi : i < m do
      let currentI := i
      have currentILt : currentI < m := by exact hi
      let row : Fin m := ⟨currentI, currentILt⟩
      let mut j := 0
      while hj : j < n do
        let currentJ := j
        have currentJLt : currentJ < n := by exact hj
        let col : Fin n := ⟨currentJ, currentJLt⟩
        out := out.push (M row col)
        j := j + 1
      i := i + 1
    return out

def entryNat (seed i j : Nat) : Nat :=
  (seed + i * 17 + j * 31 + i * j * 7 + 3) % 17

def entryRat (seed i j : Nat) : Rat :=
  (entryNat seed i j : Rat)

def entryRatPattern (pattern : String) (seed m n i j : Nat) : Rat :=
  if pattern == "diagonal" then
    if i == j then (1 + seed % 3 : Nat) else 0
  else if pattern == "dense_full_rank" then
    if i == j then (3 * (m + n + 1) + 1 : Nat) else (entryNat seed i j % 3 : Nat)
  else if pattern == "swap_heavy" then
    if m = 0 then 0 else if i == (j + 1) % m then 1 else 0
  else if pattern == "rank_deficient" then
    if i >= (2 * m) / 3 then 0 else (entryNat seed (i % max 1 (m / 3)) j % 5 : Nat)
  else if pattern == "sparse_late_pivot" then
    if j < n / 2 then 0 else if m = 0 then 0 else if i == (j - n / 2) % m then 1 else 0
  else if pattern == "already_echelon" then
    if i == j then 1 else if i < j then (entryNat seed i j % 3 : Nat) else 0
  else
    entryRat seed i j

def pivotEntry (pattern : String) (seed m n i j : Nat) : Rat :=
  let nonzero : Rat := (1 + seed % 3 : Nat)
  if pattern == "first_entry" then
    if i == 0 && j == 0 then nonzero else 0
  else if pattern == "late_row" then
    if i + 1 == m && j == 0 then nonzero else 0
  else if pattern == "late_column" then
    if i == 0 && j + 1 == n then nonzero else 0
  else if pattern == "last_entry" then
    if i + 1 == m && j + 1 == n then nonzero else 0
  else
    0

def denseNat (m n seed : Nat) : DenseMatrix m n Nat :=
  DenseMatrix.of fun i j => entryNat seed i.val j.val

def matrixNat (m n seed : Nat) : Matrix (Fin m) (Fin n) Nat :=
  Matrix.of fun i j => entryNat seed i.val j.val

def denseRat (m n : Nat) (pattern : String) (seed : Nat) : DenseMatrix m n Rat :=
  DenseMatrix.of fun i j => entryRatPattern pattern seed m n i.val j.val

def matrixRat (m n : Nat) (pattern : String) (seed : Nat) : Matrix (Fin m) (Fin n) Rat :=
  Matrix.of fun i j => entryRatPattern pattern seed m n i.val j.val

def densePivot (m n : Nat) (pattern : String) (seed : Nat) : DenseMatrix m n Rat :=
  DenseMatrix.of fun i j => pivotEntry pattern seed m n i.val j.val

def matrixPivot (m n : Nat) (pattern : String) (seed : Nat) : Matrix (Fin m) (Fin n) Rat :=
  Matrix.of fun i j => pivotEntry pattern seed m n i.val j.val

def nativeNatArray (m n seed : Nat) : Array Nat :=
  Id.run do
    let mut out := Array.mkEmpty (m * n)
    for i in [0:m] do
      for j in [0:n] do
        out := out.push (entryNat seed i j)
    return out

def nativeRatArray (m n : Nat) (pattern : String) (seed : Nat) : Array Rat :=
  Id.run do
    let mut out := Array.mkEmpty (m * n)
    for i in [0:m] do
      for j in [0:n] do
        out := out.push (entryRatPattern pattern seed m n i j)
    return out

def nativePivotArray (m n : Nat) (pattern : String) (seed : Nat) : Array Rat :=
  Id.run do
    let mut out := Array.mkEmpty (m * n)
    for i in [0:m] do
      for j in [0:n] do
        out := out.push (pivotEntry pattern seed m n i j)
    return out

def finMod (n : Nat) (hn : 0 < n) (x : Nat) : Fin n :=
  ⟨x % n, Nat.mod_lt x hn⟩

def batchUInt64 (batch : Nat) (kernel : Nat → UInt64) : UInt64 :=
  Id.run do
    let mut acc : UInt64 := 0
    for iteration in [0:batch] do
      acc := mix acc (kernel iteration)
    return acc

def calibrateBatch (kernel : Nat → UInt64) : IO Nat := do
  let mut batch := 1
  let mut finished := false
  while !finished do
    let start ← IO.monoNanosNow
    let checksum ← opaquePure (batchUInt64 batch kernel)
    let stop ← IO.monoNanosNow
    if checksum == 0 then
      IO.eprintln "unexpected zero calibration checksum"
    if stop - start >= 20000000 || batch >= 1048576 then
      finished := true
    else
      batch := batch * 2
  return batch

def scanDenseChecked {m n : Nat} (M : DenseMatrix m n Nat) (salt : Nat) : UInt64 :=
  Id.run do
    let mut acc := mix 0 (hash salt)
    let mut i := 0
    while hi : i < m do
      let currentI := i
      have currentILt : currentI < m := by exact hi
      let row : Fin m := ⟨currentI, currentILt⟩
      let mut j := 0
      while hj : j < n do
        let currentJ := j
        have currentJLt : currentJ < n := by exact hj
        let col : Fin n := ⟨currentJ, currentJLt⟩
        acc := mix acc (hash (M.get row col))
        j := j + 1
      i := i + 1
    return acc

def scanDenseUnchecked {m n : Nat} (M : DenseMatrix m n Nat) (salt : Nat) : UInt64 :=
  Id.run do
    let mut acc := mix 0 (hash salt)
    for i in [0:m] do
      for j in [0:n] do
        acc := mix acc (hash (M.get! i j))
    return acc

def scanDenseFlat {m n : Nat} (M : DenseMatrix m n Nat) (salt : Nat) : UInt64 :=
  Id.run do
    let mut acc := mix 0 (hash salt)
    for value in M.data.toArray do
      acc := mix acc (hash value)
    return acc

def scanMatrixCall {m n : Nat} (M : Matrix (Fin m) (Fin n) Nat) (salt : Nat) : UInt64 :=
  Id.run do
    let mut acc := mix 0 (hash salt)
    let mut i := 0
    while hi : i < m do
      let currentI := i
      have currentILt : currentI < m := by exact hi
      let row : Fin m := ⟨currentI, currentILt⟩
      let mut j := 0
      while hj : j < n do
        let currentJ := j
        have currentJLt : currentJ < n := by exact hj
        let col : Fin n := ⟨currentJ, currentJLt⟩
        acc := mix acc (hash (M row col))
        j := j + 1
      i := i + 1
    return acc

def denseTransposePositive {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (input : DenseMatrix m n Nat) : DenseMatrix n m Nat :=
  letI : NeZero m := ⟨by omega⟩
  letI : NeZero n := ⟨by omega⟩
  DenseMatrix.transpose input

def denseMulPositive {m k n : Nat} (hm : 0 < m) (hk : 0 < k) (hn : 0 < n)
    (A : DenseMatrix m k Nat) (B : DenseMatrix k n Nat) : DenseMatrix m n Nat :=
  letI : NeZero m := ⟨by omega⟩
  letI : NeZero k := ⟨by omega⟩
  letI : NeZero n := ⟨by omega⟩
  DenseMatrix.mul A B

def nativeTranspose (m n : Nat) (input : Array Nat) : Array Nat :=
  Id.run do
    let mut out := Array.mkEmpty (m * n)
    for i in [0:n] do
      for j in [0:m] do
        out := out.push input[j * n + i]!
    return out

def nativeDot (_m k n : Nat) (A B : Array Nat) (i j : Nat) : Nat :=
  Id.run do
    let mut sum := 0
    let rowBase := i * k
    for l in [0:k] do
      sum := sum + A[rowBase + l]! * B[l * n + j]!
    return sum

@[noinline]
def nativeMultiply (m k n : Nat) (A B : Array Nat) : Array Nat :=
  Id.run do
    let mut out := Array.mkEmpty (m * n)
    for i in [0:m] do
      let rowBase := i * k
      for j in [0:n] do
        let mut sum := 0
        for l in [0:k] do
          sum := sum + A[rowBase + l]! * B[l * n + j]!
        out := out.push sum
    return out

def nativePersistentSwapRow (m n : Nat) (input : Array Rat) (r1 r2 : Nat) : Array Rat :=
  Id.run do
    let mut out := Array.mkEmpty (m * n)
    for i in [0:m] do
      let sourceRow := if i == r1 then r2 else if i == r2 then r1 else i
      let sourceBase := sourceRow * n
      for j in [0:n] do
        out := out.push input[sourceBase + j]!
    return out

def nativePersistentScaleRow (m n : Nat) (input : Array Rat) (row : Nat) (c : Rat) : Array Rat :=
  Id.run do
    let mut out := Array.mkEmpty (m * n)
    for i in [0:m] do
      let sourceBase := i * n
      for j in [0:n] do
        let value := input[sourceBase + j]!
        out := out.push (if i == row then c * value else value)
    return out

def nativePersistentReplaceRow
    (m n : Nat) (input : Array Rat) (src tgt : Nat) (c : Rat) : Array Rat :=
  Id.run do
    let mut out := Array.mkEmpty (m * n)
    let sourceBase := src * n
    for i in [0:m] do
      let targetBase := i * n
      for j in [0:n] do
        let value := input[targetBase + j]!
        out := out.push (if i == tgt then value + c * input[sourceBase + j]! else value)
    return out

@[noinline]
def nativeLinearSwapRow (n : Nat) (input : Array Rat) (r1 r2 : Nat) : Array Rat :=
  Id.run do
    let mut out := input
    for j in [0:n] do
      let left := out[r1 * n + j]!
      let right := out[r2 * n + j]!
      out := out.set! (r1 * n + j) right
      out := out.set! (r2 * n + j) left
    return out

@[noinline]
def nativeLinearScaleRow (n : Nat) (input : Array Rat) (row : Nat) (c : Rat) : Array Rat :=
  Id.run do
    let mut out := input
    let base := row * n
    for j in [0:n] do
      out := out.set! (base + j) (c * out[base + j]!)
    return out

@[noinline]
def nativeLinearReplaceRow (n : Nat) (input : Array Rat) (src tgt : Nat) (c : Rat) : Array Rat :=
  Id.run do
    let mut out := input
    let sourceBase := src * n
    let targetBase := tgt * n
    for j in [0:n] do
      out := out.set! (targetBase + j) (out[targetBase + j]! + c * out[sourceBase + j]!)
    return out

def nativeCheckPivot (m n : Nat) (input : Array Rat) (startRow startCol : Nat) :
    Option (Nat × Nat) :=
  Id.run do
    let mut col := startCol
    while col < n do
      let mut row := startRow
      while row < m do
        if input[row * n + col]! != 0 then
          return some (row, col)
        row := row + 1
      col := col + 1
    return none

def pivotCoordinates {m n : Nat} (pivot : Option (Fin m × Fin n)) : Option (Nat × Nat) :=
  pivot.map fun location => (location.1.val, location.2.val)

def pivotFingerprint (pivot : Option (Nat × Nat)) : UInt64 :=
  match pivot with
  | none => 0
  | some (row, col) => mix (hash row) (hash col)

def normalizeDenseSteps {m : Nat} (steps : List (DenseMatrix.RowOp m Rat)) : Array UInt64 :=
  Id.run do
    let mut out := Array.mkEmpty steps.length
    for step in steps do
      let code := match step with
        | .swap row1 row2 => mix (mix 1 (hash row1.val)) (hash row2.val)
        | .factor row c => mix (mix 2 (hash row.val)) (hash c)
        | .replace src tgt c => mix (mix (mix 3 (hash src.val)) (hash tgt.val)) (hash c)
      out := out.push code
    return out

def normalizeMatrixSteps {m : Nat} (steps : List (_root_.RowOp m Rat)) : Array UInt64 :=
  Id.run do
    let mut out := Array.mkEmpty steps.length
    for step in steps do
      let code := match step with
        | .swap row1 row2 => mix (mix 1 (hash row1.val)) (hash row2.val)
        | .factor row c => mix (mix 2 (hash row.val)) (hash c)
        | .replace src tgt c => mix (mix (mix 3 (hash src.val)) (hash tgt.val)) (hash c)
      out := out.push code
    return out

def rawDenseRef {m n : Nat} (input : DenseMatrix m n Rat) : ReductionOutput :=
  let raw := DenseMatrix.GaussianEliminationInternal.rawRowEchelonForm input
  { data := raw.1.data.toArray, steps := normalizeDenseSteps raw.2 }

def rawDenseRref {m n : Nat} (input : DenseMatrix m n Rat) : ReductionOutput :=
  let raw := DenseMatrix.GaussianEliminationInternal.rawReducedRowEchelonForm input
  { data := raw.1.data.toArray, steps := normalizeDenseSteps raw.2 }

def rawMatrixRef {m n : Nat} (input : Matrix (Fin m) (Fin n) Rat) : ReductionOutput :=
  let raw := GaussianEliminationInternal.rawRowEchelonForm input
  { data := materializeMatrix raw.1, steps := normalizeMatrixSteps raw.2 }

def rawMatrixRref {m n : Nat} (input : Matrix (Fin m) (Fin n) Rat) : ReductionOutput :=
  let raw := GaussianEliminationInternal.rawReducedRowEchelonForm input
  { data := materializeMatrix raw.1, steps := normalizeMatrixSteps raw.2 }

def makeMeta (cfg : BenchConfig)
    (suite operation variant implementation coefficient pattern : String)
    (shape : Shape) (sample batch : Nat) : BenchMeta :=
  { suite, operation, variantName := variant, implementation, coefficient,
    pattern,
    rows := shape.rows, inner := shape.inner, cols := shape.cols,
    processRun := cfg.processRun, sample, batch }

def measureValue {σ α : Type} (info : BenchMeta) (setup : IO σ) (run : σ → α)
    (consume : α → UInt64) : IO BenchSample := do
  let input ← setup
  let startHb ← IO.getNumHeartbeats
  let start ← IO.monoNanosNow
  let output ← opaquePure (run input)
  let stop ← IO.monoNanosNow
  let stopHb ← IO.getNumHeartbeats
  let checksum := consume output
  return BenchSample.mk info.suite info.operation info.variantName
    info.implementation info.coefficient info.pattern info.rows info.inner info.cols
    info.processRun info.sample info.batch
    (stop - start) (stopHb - startHb) checksum

def measureSetup {σ : Type} (info : BenchMeta) (setup : Unit → σ) (consume : σ → UInt64) :
    IO BenchSample := do
  let startHb ← IO.getNumHeartbeats
  let start ← IO.monoNanosNow
  let input ← opaquePure (setup ())
  let stop ← IO.monoNanosNow
  let stopHb ← IO.getNumHeartbeats
  let checksum := consume input
  return BenchSample.mk info.suite info.operation info.variantName
    info.implementation info.coefficient info.pattern info.rows info.inner info.cols
    info.processRun info.sample info.batch
    (stop - start) (stopHb - startHb) checksum

def sampleSeed (cfg : BenchConfig) (round : Nat) : Nat :=
  cfg.seed + cfg.processRun * 1000003 + round * 7919

def rotate {α : Type u} (items : List α) (offset : Nat) : List α :=
  match items.length with
  | 0 => []
  | count + 1 =>
    let split := offset % (count + 1)
    items.drop split ++ items.take split

def runCase (cfg : BenchConfig) (variants : List String)
    (measure : Nat → String → IO BenchSample) : IO (List BenchSample) := do
  for warmup in [0:warmups cfg] do
    for variant in rotate variants warmup do
      discard <| measure (100000 + warmup) variant
  let mut out : List BenchSample := []
  for sample in [0:recordedSamples cfg] do
    for variant in rotate variants sample do
      out := (← measure sample variant) :: out
  return out.reverse

def failValidation {α : Type} (suite operation details : String) : IO α :=
  throw <| IO.userError s!"validation failed: suite={suite} operation={operation} {details}"

def requireArrayEqual {α : Type u} [BEq α] (suite operation details : String)
    (left right : Array α) : IO Unit :=
  if left == right then pure () else failValidation suite operation details

def requireEqual {α : Type u} [BEq α] (suite operation details : String) (left right : α) :
    IO Unit :=
  if left == right then pure () else failValidation suite operation details

def shapeContext (m n seed : Nat) : String :=
  s!"shape={m}x{n} seed={seed}"

def productContext (m k n seed : Nat) : String :=
  s!"shape={m}x{k}x{n} seed={seed}"

def patternedContext (m n seed : Nat) (pattern : String) : String :=
  s!"shape={m}x{n} pattern={pattern} seed={seed}"

def suiteAccessCase (cfg : BenchConfig) (m n : Nat) : IO (List BenchSample) := do
  let shape : Shape := { rows := m, inner := 0, cols := n }
  let validationSeed := sampleSeed cfg 0
  let dense := denseNat m n validationSeed
  let matrix := matrixNat m n validationSeed
  let checked := scanDenseChecked dense 0
  let unchecked := scanDenseUnchecked dense 0
  let flat := scanDenseFlat dense 0
  let called := scanMatrixCall matrix 0
  let context := shapeContext m n validationSeed
  let _validation ← requireEqual "access" "scan" context checked unchecked
  let _validation ← requireEqual "access" "scan" context checked flat
  let _validation ← requireEqual "access" "scan" context checked called
  let batch ← calibrateBatch fun iteration => scanDenseChecked dense iteration
  let measure := fun round implementation =>
    let seed := sampleSeed cfg round
    match implementation with
    | "dense_checked" =>
      measureValue
        (makeMeta cfg "access" "scan" "dense_api" "dense_checked" "Nat" "deterministic"
          shape round batch)
        (pure (denseNat m n seed))
        (fun input =>
          batchUInt64 batch fun iteration => scanDenseChecked input (round + iteration)) id
    | "dense_unchecked" =>
      measureValue
        (makeMeta cfg "access" "scan" "dense_api" "dense_unchecked" "Nat" "deterministic"
          shape round batch)
        (pure (denseNat m n seed))
        (fun input =>
          batchUInt64 batch fun iteration => scanDenseUnchecked input (round + iteration)) id
    | "dense_flat" =>
      measureValue
        (makeMeta cfg "access" "scan" "dense_native" "dense_flat" "Nat" "deterministic"
          shape round batch)
        (pure (denseNat m n seed))
        (fun input => batchUInt64 batch fun iteration => scanDenseFlat input (round + iteration)) id
    | "matrix_call" =>
      measureValue
        (makeMeta cfg "access" "scan" "matrix_api" "matrix_call" "Nat" "deterministic"
          shape round batch)
        (pure (matrixNat m n seed))
        (fun input =>
          batchUInt64 batch fun iteration => scanMatrixCall input (round + iteration)) id
    | _ => throw <| IO.userError s!"unknown access implementation {implementation}"
  runCase cfg ["dense_checked", "dense_unchecked", "dense_flat", "matrix_call"] measure

def suiteConstructionCase (cfg : BenchConfig) (m n : Nat) : IO (List BenchSample) := do
  let shape : Shape := { rows := m, inner := 0, cols := n }
  let validationSeed := sampleSeed cfg 0
  let denseOut := (denseNat m n validationSeed).data.toArray
  let nativeOut := nativeNatArray m n validationSeed
  let matrixOut := materializeMatrix (matrixNat m n validationSeed)
  let context := shapeContext m n validationSeed
  let _validation ← requireArrayEqual "construction" "construct" context denseOut nativeOut
  let _validation ← requireArrayEqual "construction" "construct" context denseOut matrixOut
  let constructMeasure := fun round implementation =>
    let seed := sampleSeed cfg round
    match implementation with
    | "dense_api" =>
      measureValue
        (makeMeta cfg "construction" "construct" "dense_api" "dense_api" "Nat" "deterministic"
          shape round 1)
        (pure seed) (fun input => (denseNat m n input).data.toArray) fingerprintNatArray
    | "dense_native" =>
      measureValue
        (makeMeta cfg "construction" "construct" "dense_native" "dense_native" "Nat" "deterministic"
          shape round 1)
        (pure seed) (fun input => nativeNatArray m n input) fingerprintNatArray
    | "matrix_api" =>
      measureValue
        (makeMeta cfg "construction" "construct" "matrix_api" "matrix_api" "Nat" "deterministic"
          shape round 1)
        (pure seed) (fun input => materializeMatrix (matrixNat m n input)) fingerprintNatArray
    | _ => throw <| IO.userError s!"unknown construction implementation {implementation}"
  let construct ← runCase cfg ["dense_api", "dense_native", "matrix_api"] constructMeasure
  let sourceMatrix := matrixNat m n validationSeed
  let ofMatrixOut := (DenseMatrix.ofMatrix sourceMatrix).data.toArray
  let _validation ← requireArrayEqual "construction" "of_matrix" context ofMatrixOut nativeOut
  let ofMatrixMeasure := fun round implementation =>
    let seed := sampleSeed cfg round
    match implementation with
    | "of_matrix" =>
      measureValue
        (makeMeta cfg "construction" "of_matrix" "dense_api" "of_matrix" "Nat" "deterministic"
          shape round 1)
        (pure (matrixNat m n seed))
        (fun input => (DenseMatrix.ofMatrix input).data.toArray) fingerprintNatArray
    | _ => throw <| IO.userError s!"unknown conversion implementation {implementation}"
  let ofMatrix ← runCase cfg ["of_matrix"] ofMatrixMeasure
  let sourceDense := denseNat m n validationSeed
  let toMatrixOut := materializeMatrix (DenseMatrix.toMatrix sourceDense)
  let _validation ← requireArrayEqual "construction" "to_matrix_materialize"
    s!"shape={m}x{n} seed={validationSeed}" toMatrixOut nativeOut
  let toMatrixMeasure := fun round implementation =>
    let seed := sampleSeed cfg round
    match implementation with
    | "to_matrix_materialize" =>
      measureValue
        (makeMeta cfg "construction" "to_matrix_materialize" "dense_api" "to_matrix_materialize"
          "Nat" "deterministic" shape round 1)
        (pure (denseNat m n seed))
        (fun input => materializeMatrix (DenseMatrix.toMatrix input)) fingerprintNatArray
    | _ => throw <| IO.userError s!"unknown conversion implementation {implementation}"
  let toMatrix ← runCase cfg ["to_matrix_materialize"] toMatrixMeasure
  return construct ++ ofMatrix ++ toMatrix

def suiteElementwiseCase (cfg : BenchConfig) (m n : Nat) : IO (List BenchSample) := do
  if hm : 0 < m then
    if hn : 0 < n then
      let shape : Shape := { rows := m, inner := 0, cols := n }
      let validationSeed := sampleSeed cfg 0
      let denseA := denseNat m n validationSeed
      let denseB := denseNat m n (validationSeed + 1)
      let matrixA := matrixNat m n validationSeed
      let matrixB := matrixNat m n (validationSeed + 1)
      let addDense := (DenseMatrix.add denseA denseB).data.toArray
      let addMatrix := materializeMatrix (matrixA + matrixB)
      let context := shapeContext m n validationSeed
      let _validation ← requireArrayEqual "elementwise" "add" context addDense addMatrix
      let scalar := 2 + validationSeed % 3
      let smulDense := (DenseMatrix.smul scalar denseA).data.toArray
      let smulMatrix := materializeMatrix (scalar • matrixA)
      let _validation ← requireArrayEqual "elementwise" "smul" context smulDense smulMatrix
      let transposeDense := (denseTransposePositive hm hn denseA).data.toArray
      let transposeNative := nativeTranspose m n denseA.data.toArray
      let transposeMatrix := materializeMatrix matrixA.transpose
      let _validation ←
        requireArrayEqual "elementwise" "transpose" context transposeDense transposeNative
      let _validation ←
        requireArrayEqual "elementwise" "transpose" context transposeDense transposeMatrix
      let addMeasure := fun round implementation =>
        let seed := sampleSeed cfg round
        match implementation with
        | "dense_api" =>
          measureValue
            (makeMeta cfg "elementwise" "add" "dense_api" "dense_api" "Nat" "deterministic"
              shape round 1)
            (pure (denseNat m n seed, denseNat m n (seed + 1)))
            (fun input => (DenseMatrix.add input.1 input.2).data.toArray) fingerprintNatArray
        | "matrix_api" =>
          measureValue
            (makeMeta cfg "elementwise" "add" "matrix_api" "matrix_api" "Nat" "deterministic"
              shape round 1)
            (pure (matrixNat m n seed, matrixNat m n (seed + 1)))
            (fun input => materializeMatrix (input.1 + input.2)) fingerprintNatArray
        | _ => throw <| IO.userError s!"unknown add implementation {implementation}"
      let add ← runCase cfg ["dense_api", "matrix_api"] addMeasure
      let smulMeasure := fun round implementation =>
        let seed := sampleSeed cfg round
        let scalar := 2 + seed % 3
        match implementation with
        | "dense_api" =>
          measureValue
            (makeMeta cfg "elementwise" "smul" "dense_api" "dense_api" "Nat" "deterministic"
              shape round 1)
            (pure (denseNat m n seed))
            (fun input => (DenseMatrix.smul scalar input).data.toArray) fingerprintNatArray
        | "matrix_api" =>
          measureValue
            (makeMeta cfg "elementwise" "smul" "matrix_api" "matrix_api" "Nat" "deterministic"
              shape round 1)
            (pure (matrixNat m n seed))
            (fun input => materializeMatrix (scalar • input)) fingerprintNatArray
        | _ => throw <| IO.userError s!"unknown smul implementation {implementation}"
      let smul ← runCase cfg ["dense_api", "matrix_api"] smulMeasure
      let transposeMeasure := fun round implementation =>
        let seed := sampleSeed cfg round
        match implementation with
        | "dense_api" =>
          measureValue
            (makeMeta cfg "elementwise" "transpose" "dense_api" "dense_api" "Nat" "deterministic"
              shape round 1)
            (pure (denseNat m n seed))
            (fun input => (denseTransposePositive hm hn input).data.toArray) fingerprintNatArray
        | "dense_native" =>
          measureValue
            (makeMeta cfg "elementwise" "transpose" "dense_native" "dense_native" "Nat"
              "deterministic" shape round 1)
            (pure (nativeNatArray m n seed))
            (fun input => nativeTranspose m n input) fingerprintNatArray
        | "matrix_api" =>
          measureValue
            (makeMeta cfg "elementwise" "transpose" "matrix_api" "matrix_api" "Nat"
              "deterministic" shape round 1)
            (pure (matrixNat m n seed))
            (fun input => materializeMatrix input.transpose) fingerprintNatArray
        | _ => throw <| IO.userError s!"unknown transpose implementation {implementation}"
      let transpose ← runCase cfg ["dense_api", "dense_native", "matrix_api"] transposeMeasure
      return add ++ smul ++ transpose
    else
      failValidation "elementwise" "shape" s!"nonpositive cols={n}"
  else
    failValidation "elementwise" "shape" s!"nonpositive rows={m}"

def matrixDot {m k n : Nat} (A : Matrix (Fin m) (Fin k) Nat) (B : Matrix (Fin k) (Fin n) Nat)
    (i : Fin m) (j : Fin n) : Nat :=
  ∑ l : Fin k, A i l * B l j

def suiteDotCase (cfg : BenchConfig) (k : Nat) : IO (List BenchSample) := do
  let m := 8
  let n := 8
  if hk : 0 < k then
    let denseDot : Fin m → Fin n → DenseMatrix m k Nat → DenseMatrix k n Nat → Nat :=
      fun row col A B =>
        letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
        DenseMatrix.dotProduct row col A B
    let hm : 0 < m := by decide
    let hn : 0 < n := by decide
    let shape : Shape := { rows := m, inner := k, cols := n }
    let validationSeed := sampleSeed cfg 0
    let denseA := denseNat m k validationSeed
    let denseB := denseNat k n (validationSeed + 1)
    let matrixA := matrixNat m k validationSeed
    let matrixB := matrixNat k n (validationSeed + 1)
    let nativeA := nativeNatArray m k validationSeed
    let nativeB := nativeNatArray k n (validationSeed + 1)
    let i := finMod m hm 1
    let j := finMod n hn 3
    let recursive := denseDot i j denseA denseB
    let finset := ∑ l : Fin k, denseA.get i l * denseB.get l j
    let native := nativeDot m k n nativeA nativeB i.val j.val
    let matrix := matrixDot matrixA matrixB i j
    let context := s!"inner={k} seed={validationSeed}"
    let _validation ← requireEqual "dot" "dot" context recursive finset
    let _validation ← requireEqual "dot" "dot" context recursive native
    let _validation ← requireEqual "dot" "dot" context recursive matrix
    let batch ← calibrateBatch fun iteration =>
      let row := finMod m hm iteration
      let col := finMod n hn (iteration * 3 + 1)
      hash (denseDot row col denseA denseB)
    let measure := fun round implementation =>
      let seed := sampleSeed cfg round
      match implementation with
      | "dense_recursive" =>
        measureValue
          (makeMeta cfg "dot" "dot" "dense_api" "dense_recursive" "Nat" "deterministic"
            shape round batch)
          (pure (denseNat m k seed, denseNat k n (seed + 1)))
          (fun input => batchUInt64 batch fun iteration =>
            let row := finMod m hm (round + iteration)
            let col := finMod n hn (round + iteration * 3 + 1)
            hash (denseDot row col input.1 input.2)) id
      | "dense_finset" =>
        measureValue
          (makeMeta cfg "dot" "dot" "dense_api" "dense_finset" "Nat" "deterministic"
            shape round batch)
          (pure (denseNat m k seed, denseNat k n (seed + 1)))
          (fun input => batchUInt64 batch fun iteration =>
            let row := finMod m hm (round + iteration)
            let col := finMod n hn (round + iteration * 3 + 1)
            hash (∑ l : Fin k, input.1.get row l * input.2.get l col)) id
      | "dense_native" =>
        measureValue
          (makeMeta cfg "dot" "dot" "dense_native" "dense_native" "Nat" "deterministic"
            shape round batch)
          (pure (nativeNatArray m k seed, nativeNatArray k n (seed + 1)))
          (fun input => batchUInt64 batch fun iteration =>
            hash (nativeDot m k n input.1 input.2 ((round + iteration) % m)
              ((round + iteration * 3 + 1) % n))) id
      | "matrix_finset" =>
        measureValue
          (makeMeta cfg "dot" "dot" "matrix_api" "matrix_finset" "Nat" "deterministic"
            shape round batch)
          (pure (matrixNat m k seed, matrixNat k n (seed + 1)))
          (fun input => batchUInt64 batch fun iteration =>
            let row := finMod m hm (round + iteration)
            let col := finMod n hn (round + iteration * 3 + 1)
            hash (matrixDot input.1 input.2 row col)) id
      | _ => throw <| IO.userError s!"unknown dot implementation {implementation}"
    runCase cfg ["dense_recursive", "dense_finset", "dense_native", "matrix_finset"] measure
  else
    failValidation "dot" "shape" s!"nonpositive inner={k}"

def suiteMulCase (cfg : BenchConfig) (m k n : Nat) : IO (List BenchSample) := do
  if hm : 0 < m then
    if hk : 0 < k then
      if hn : 0 < n then
        let shape : Shape := { rows := m, inner := k, cols := n }
        let validationSeed := sampleSeed cfg 0
        let denseA := denseNat m k validationSeed
        let denseB := denseNat k n (validationSeed + 1)
        let matrixA := matrixNat m k validationSeed
        let matrixB := matrixNat k n (validationSeed + 1)
        let nativeA := nativeNatArray m k validationSeed
        let nativeB := nativeNatArray k n (validationSeed + 1)
        let denseOut := (denseMulPositive hm hk hn denseA denseB).data.toArray
        let nativeOut := nativeMultiply m k n nativeA nativeB
        let matrixOut := materializeMatrix (matrixA * matrixB)
        let context := productContext m k n validationSeed
        let _validation ← requireArrayEqual "mul" "mul" context denseOut nativeOut
        let _validation ← requireArrayEqual "mul" "mul" context denseOut matrixOut
        let measure := fun round implementation =>
          let seed := sampleSeed cfg round
          match implementation with
          | "dense_api" =>
            measureValue
              (makeMeta cfg "mul" "mul" "dense_api" "dense_api" "Nat" "deterministic"
                shape round 1)
              (pure (denseNat m k seed, denseNat k n (seed + 1)))
              (fun input => (denseMulPositive hm hk hn input.1 input.2).data.toArray)
              fingerprintNatArray
          | "dense_native" =>
            measureValue
              (makeMeta cfg "mul" "mul" "dense_native" "dense_native" "Nat" "deterministic"
                shape round 1)
              (pure (nativeNatArray m k seed, nativeNatArray k n (seed + 1)))
              (fun input => nativeMultiply m k n input.1 input.2) fingerprintNatArray
          | "matrix_api" =>
            measureValue
              (makeMeta cfg "mul" "mul" "matrix_api" "matrix_api" "Nat" "deterministic"
                shape round 1)
              (pure (matrixNat m k seed, matrixNat k n (seed + 1)))
              (fun input => materializeMatrix (input.1 * input.2)) fingerprintNatArray
          | _ => throw <| IO.userError s!"unknown multiplication implementation {implementation}"
        runCase cfg ["dense_api", "dense_native", "matrix_api"] measure
      else
        failValidation "mul" "shape" s!"nonpositive cols={n}"
    else
      failValidation "mul" "shape" s!"nonpositive inner={k}"
  else
    failValidation "mul" "shape" s!"nonpositive rows={m}"

def suiteRowCase (cfg : BenchConfig) (m n : Nat) (scalingPattern : String) :
    IO (List BenchSample) := do
  if hm : 1 < m then
    if hn : 0 < n then
      let shape : Shape := { rows := m, inner := 0, cols := n }
      let validationSeed := sampleSeed cfg 0
      let sourceDense := denseRat m n "dense_full_rank" validationSeed
      let sourceMatrix := matrixRat m n "dense_full_rank" validationSeed
      let sourceNative := nativeRatArray m n "dense_full_rank" validationSeed
      let row1 : Fin m := ⟨0, by omega⟩
      let row2 : Fin m := ⟨m - 1, by omega⟩
      let row : Fin m := ⟨m / 2, by omega⟩
      let scale : Rat := 2
      let replace : Rat := 3
      let context := shapeContext m n validationSeed
      let swapDense := (DenseMatrix.swapRow sourceDense row1 row2).data.toArray
      let swapNative := nativePersistentSwapRow m n sourceNative row1.val row2.val
      let swapLinear := nativeLinearSwapRow n sourceNative row1.val row2.val
      let swapMatrix := materializeMatrix (_root_.swapRow sourceMatrix row1 row2)
      let _validation ← requireArrayEqual "row_ops" "swap_row" context swapDense swapNative
      let _validation ← requireArrayEqual "row_ops" "swap_row" context swapDense swapLinear
      let _validation ← requireArrayEqual "row_ops" "swap_row" context swapDense swapMatrix
      let scaleDense := (DenseMatrix.scaleRow sourceDense row scale).data.toArray
      let scaleNative := nativePersistentScaleRow m n sourceNative row.val scale
      let scaleLinear := nativeLinearScaleRow n sourceNative row.val scale
      let scaleMatrix := materializeMatrix (_root_.factor sourceMatrix row scale)
      let _validation ← requireArrayEqual "row_ops" "scale_row" context scaleDense scaleNative
      let _validation ← requireArrayEqual "row_ops" "scale_row" context scaleDense scaleLinear
      let _validation ← requireArrayEqual "row_ops" "scale_row" context scaleDense scaleMatrix
      let replaceDense := (DenseMatrix.replaceRow sourceDense row1 row2 replace).data.toArray
      let replaceNative := nativePersistentReplaceRow m n sourceNative row1.val row2.val replace
      let replaceLinear := nativeLinearReplaceRow n sourceNative row1.val row2.val replace
      let replaceMatrix := materializeMatrix (_root_.replace sourceMatrix row1 row2 replace)
      let _validation ←
        requireArrayEqual "row_ops" "replace_row" context replaceDense replaceNative
      let _validation ←
        requireArrayEqual "row_ops" "replace_row" context replaceDense replaceLinear
      let _validation ←
        requireArrayEqual "row_ops" "replace_row" context replaceDense replaceMatrix
      let swapMeasure := fun round implementation =>
        let seed := sampleSeed cfg round
        match implementation with
        | "dense_api" =>
          measureValue
            (makeMeta cfg "row_ops" "swap_row" "dense_api" "dense_api" "Rat" scalingPattern
              shape round 1)
            (pure (denseRat m n "dense_full_rank" seed))
            (fun input => (DenseMatrix.swapRow input row1 row2).data.toArray) fingerprintRatArray
        | "dense_native" =>
          measureValue
            (makeMeta cfg "row_ops" "swap_row" "dense_native" "dense_native" "Rat"
              scalingPattern shape round 1)
            (pure (nativeRatArray m n "dense_full_rank" seed))
            (fun input => nativePersistentSwapRow m n input row1.val row2.val) fingerprintRatArray
        | "dense_native_linear" =>
          measureValue
            (makeMeta cfg "row_ops" "swap_row" "dense_native_linear" "dense_native_linear"
              "Rat" scalingPattern shape round 1)
            (pure (nativeRatArray m n "dense_full_rank" seed))
            (fun input => nativeLinearSwapRow n input row1.val row2.val) fingerprintRatArray
        | "matrix_api" =>
          measureValue
            (makeMeta cfg "row_ops" "swap_row" "matrix_api" "matrix_api" "Rat" scalingPattern
              shape round 1)
            (pure (matrixRat m n "dense_full_rank" seed))
            (fun input => materializeMatrix (_root_.swapRow input row1 row2)) fingerprintRatArray
        | _ => throw <| IO.userError s!"unknown swap-row implementation {implementation}"
      let swap ←
        runCase cfg ["dense_api", "dense_native", "dense_native_linear", "matrix_api"] swapMeasure
      let scaleMeasure := fun round implementation =>
        let seed := sampleSeed cfg round
        match implementation with
        | "dense_api" =>
          measureValue
            (makeMeta cfg "row_ops" "scale_row" "dense_api" "dense_api" "Rat" scalingPattern
              shape round 1)
            (pure (denseRat m n "dense_full_rank" seed))
            (fun input => (DenseMatrix.scaleRow input row scale).data.toArray) fingerprintRatArray
        | "dense_native" =>
          measureValue
            (makeMeta cfg "row_ops" "scale_row" "dense_native" "dense_native" "Rat"
              scalingPattern shape round 1)
            (pure (nativeRatArray m n "dense_full_rank" seed))
            (fun input => nativePersistentScaleRow m n input row.val scale) fingerprintRatArray
        | "dense_native_linear" =>
          measureValue
            (makeMeta cfg "row_ops" "scale_row" "dense_native_linear" "dense_native_linear"
              "Rat" scalingPattern shape round 1)
            (pure (nativeRatArray m n "dense_full_rank" seed))
            (fun input => nativeLinearScaleRow n input row.val scale) fingerprintRatArray
        | "matrix_api" =>
          measureValue
            (makeMeta cfg "row_ops" "scale_row" "matrix_api" "matrix_api" "Rat" scalingPattern
              shape round 1)
            (pure (matrixRat m n "dense_full_rank" seed))
            (fun input => materializeMatrix (_root_.factor input row scale)) fingerprintRatArray
        | _ => throw <| IO.userError s!"unknown scale-row implementation {implementation}"
      let scaleOut ←
        runCase cfg ["dense_api", "dense_native", "dense_native_linear", "matrix_api"] scaleMeasure
      let replaceMeasure := fun round implementation =>
        let seed := sampleSeed cfg round
        match implementation with
        | "dense_api" =>
          measureValue
            (makeMeta cfg "row_ops" "replace_row" "dense_api" "dense_api" "Rat"
              scalingPattern shape round 1)
            (pure (denseRat m n "dense_full_rank" seed))
            (fun input => (DenseMatrix.replaceRow input row1 row2 replace).data.toArray)
            fingerprintRatArray
        | "dense_native" =>
          measureValue
            (makeMeta cfg "row_ops" "replace_row" "dense_native" "dense_native" "Rat"
              scalingPattern shape round 1)
            (pure (nativeRatArray m n "dense_full_rank" seed))
            (fun input => nativePersistentReplaceRow m n input row1.val row2.val replace)
            fingerprintRatArray
        | "dense_native_linear" =>
          measureValue
            (makeMeta cfg "row_ops" "replace_row" "dense_native_linear" "dense_native_linear"
              "Rat" scalingPattern shape round 1)
            (pure (nativeRatArray m n "dense_full_rank" seed))
            (fun input => nativeLinearReplaceRow n input row1.val row2.val replace)
            fingerprintRatArray
        | "matrix_api" =>
          measureValue
            (makeMeta cfg "row_ops" "replace_row" "matrix_api" "matrix_api" "Rat"
              scalingPattern shape round 1)
            (pure (matrixRat m n "dense_full_rank" seed))
            (fun input => materializeMatrix (_root_.replace input row1 row2 replace))
            fingerprintRatArray
        | _ => throw <| IO.userError s!"unknown replace-row implementation {implementation}"
      let replaceOut ←
        runCase cfg ["dense_api", "dense_native", "dense_native_linear", "matrix_api"]
          replaceMeasure
      return swap ++ scaleOut ++ replaceOut
    else
      failValidation "row_ops" "shape" s!"nonpositive cols={n}"
  else
    failValidation "row_ops" "shape" s!"requires at least two rows, got {m}"

def suitePivotCase (cfg : BenchConfig) (m n : Nat) (pattern : String) : IO (List BenchSample) := do
  if _hm : 0 < m then
    if _hn : 0 < n then
      let shape : Shape := { rows := m, inner := 0, cols := n }
      let validationSeed := sampleSeed cfg 0
      let dense := densePivot m n pattern validationSeed
      let matrix := matrixPivot m n pattern validationSeed
      let native := nativePivotArray m n pattern validationSeed
      let densePivotLocation := pivotCoordinates (DenseMatrix.checkPivot dense 0 0)
      let matrixPivotLocation := pivotCoordinates (_root_.checkPivot matrix 0 0)
      let nativePivotLocation := nativeCheckPivot m n native 0 0
      let context := patternedContext m n validationSeed pattern
      let _validation ←
        requireEqual "pivot" "check_pivot" context densePivotLocation nativePivotLocation
      let _validation ←
        requireEqual "pivot" "check_pivot" context densePivotLocation matrixPivotLocation
      let batch ← calibrateBatch fun iteration =>
        pivotFingerprint <| pivotCoordinates <|
          DenseMatrix.checkPivot dense (iteration % m) ((iteration * 3 + 1) % n)
      let measure := fun round implementation =>
        let seed := sampleSeed cfg round
        match implementation with
        | "dense_api" =>
          measureValue
            (makeMeta cfg "pivot" "check_pivot" "dense_api" "dense_api" "Rat" pattern
              shape round batch)
            (pure (densePivot m n pattern seed))
            (fun input => batchUInt64 batch fun iteration =>
              pivotFingerprint <| pivotCoordinates <|
                DenseMatrix.checkPivot input ((round + iteration) % m)
                  ((round + iteration * 3 + 1) % n)) id
        | "dense_native" =>
          measureValue
            (makeMeta cfg "pivot" "check_pivot" "dense_native" "dense_native" "Rat" pattern
              shape round batch)
            (pure (nativePivotArray m n pattern seed))
            (fun input => batchUInt64 batch fun iteration =>
              pivotFingerprint <| nativeCheckPivot m n input ((round + iteration) % m)
                ((round + iteration * 3 + 1) % n)) id
        | "matrix_api" =>
          measureValue
            (makeMeta cfg "pivot" "check_pivot" "matrix_api" "matrix_api" "Rat" pattern
              shape round batch)
            (pure (matrixPivot m n pattern seed))
            (fun input => batchUInt64 batch fun iteration =>
              pivotFingerprint <| pivotCoordinates <|
                _root_.checkPivot input ((round + iteration) % m)
                  ((round + iteration * 3 + 1) % n)) id
        | _ => throw <| IO.userError s!"unknown pivot implementation {implementation}"
      runCase cfg ["dense_api", "dense_native", "matrix_api"] measure
    else
      failValidation "pivot" "shape" s!"nonpositive cols={n}"
  else
    failValidation "pivot" "shape" s!"nonpositive rows={m}"

def suiteRrefCase (cfg : BenchConfig) (operation pattern : String) (m n : Nat) :
    IO (List BenchSample) := do
  let shape : Shape := { rows := m, inner := 0, cols := n }
  let validationSeed := sampleSeed cfg 0
  let denseInput := denseRat m n pattern validationSeed
  let matrixInput := matrixRat m n pattern validationSeed
  let denseOutput :=
    if operation == "ref" then rawDenseRef denseInput else rawDenseRref denseInput
  let matrixOutput :=
    if operation == "ref" then rawMatrixRef matrixInput else rawMatrixRref matrixInput
  let context := patternedContext m n validationSeed pattern
  let _validation ← requireArrayEqual "rref" operation context denseOutput.data matrixOutput.data
  let _validation ←
    requireArrayEqual "rref" operation context denseOutput.steps matrixOutput.steps
  let measure := fun round implementation =>
    let seed := sampleSeed cfg round
    match implementation, operation with
    | "dense_api", "ref" =>
      measureValue
        (makeMeta cfg "rref" "ref" "dense_api" "dense_api" "Rat" pattern shape round 1)
        (pure (denseRat m n pattern seed)) rawDenseRef fingerprintReduction
    | "matrix_api", "ref" =>
      measureValue
        (makeMeta cfg "rref" "ref" "matrix_api" "matrix_api" "Rat" pattern shape round 1)
        (pure (matrixRat m n pattern seed)) rawMatrixRef fingerprintReduction
    | "dense_api", "rref" =>
      measureValue
        (makeMeta cfg "rref" "rref" "dense_api" "dense_api" "Rat" pattern shape round 1)
        (pure (denseRat m n pattern seed)) rawDenseRref fingerprintReduction
    | "matrix_api", "rref" =>
      measureValue
        (makeMeta cfg "rref" "rref" "matrix_api" "matrix_api" "Rat" pattern shape round 1)
        (pure (matrixRat m n pattern seed)) rawMatrixRref fingerprintReduction
    | _, _ => throw <| IO.userError s!"unknown RREF implementation {implementation}"
  runCase cfg ["dense_api", "matrix_api"] measure

def suiteControlCase (cfg : BenchConfig) (m n : Nat) : IO (List BenchSample) := do
  let shape : Shape := { rows := m, inner := 0, cols := n }
  let validationSeed := sampleSeed cfg 0
  let native := nativeNatArray m n validationSeed
  let matrix := materializeMatrix (matrixNat m n validationSeed)
  let context := shapeContext m n validationSeed
  let _validation ← requireArrayEqual "control" "input_setup" context native matrix
  let consumeMeasure := fun round implementation =>
    match implementation with
    | "control" =>
      let seed := sampleSeed cfg round
      measureValue
        (makeMeta cfg "control" "consume_array" "control" "control" "Nat" "deterministic"
          shape round 1)
        (pure (nativeNatArray m n seed)) fingerprintNatArray id
    | _ => throw <| IO.userError s!"unknown control implementation {implementation}"
  let consume ← runCase cfg ["control"] consumeMeasure
  let materializeMeasure := fun round implementation =>
    match implementation with
    | "control" =>
      let seed := sampleSeed cfg round
      measureValue
        (makeMeta cfg "control" "materialize_matrix" "control" "control" "Nat" "deterministic"
          shape round 1)
        (pure (matrixNat m n seed)) materializeMatrix fingerprintNatArray
    | _ => throw <| IO.userError s!"unknown control implementation {implementation}"
  let materialize ← runCase cfg ["control"] materializeMeasure
  let setupMeasure := fun round implementation =>
    match implementation with
    | "control" =>
      let seed := sampleSeed cfg round
      measureSetup
        (makeMeta cfg "control" "input_setup" "control" "control" "Nat" "deterministic"
          shape round 1)
        (fun _ => nativeNatArray m n seed) fingerprintNatArray
    | _ => throw <| IO.userError s!"unknown control implementation {implementation}"
  let setup ← runCase cfg ["control"] setupMeasure
  return consume ++ materialize ++ setup

def selected {α : Type u} (cfg : BenchConfig) (items : List α) : List α :=
  if cfg.profile == "smoke" then items.take 1 else items

def collectCases {α : Type u} (items : List α) (run : α → IO (List BenchSample)) :
    IO (List BenchSample) := do
  let mut out : List BenchSample := []
  for item in items do
    out := out ++ (← run item)
  return out

def accessShapes : List Shape :=
  [ { rows := 128, inner := 0, cols := 128 }, { rows := 512, inner := 0, cols := 64 },
    { rows := 64, inner := 0, cols := 512 }, { rows := 256, inner := 0, cols := 256 },
    { rows := 1024, inner := 0, cols := 64 }, { rows := 64, inner := 0, cols := 1024 } ]

def constructionShapes : List Shape :=
  [ { rows := 64, inner := 0, cols := 64 }, { rows := 256, inner := 0, cols := 64 },
    { rows := 64, inner := 0, cols := 256 }, { rows := 256, inner := 0, cols := 256 },
    { rows := 512, inner := 0, cols := 128 }, { rows := 128, inner := 0, cols := 512 } ]

def elementwiseShapes : List Shape :=
  [ { rows := 64, inner := 0, cols := 64 }, { rows := 128, inner := 0, cols := 128 },
    { rows := 256, inner := 0, cols := 256 }, { rows := 64, inner := 0, cols := 1024 },
    { rows := 1024, inner := 0, cols := 64 } ]

def dotDimensions : List Nat := [64, 256, 1024, 4096, 16384]

def mulShapes : List Shape :=
  [ { rows := 8, inner := 8, cols := 8 }, { rows := 16, inner := 16, cols := 16 },
    { rows := 24, inner := 24, cols := 24 }, { rows := 32, inner := 32, cols := 32 },
    { rows := 40, inner := 40, cols := 40 }, { rows := 8, inner := 256, cols := 8 },
    { rows := 64, inner := 16, cols := 64 }, { rows := 16, inner := 128, cols := 64 },
    { rows := 64, inner := 128, cols := 16 }, { rows := 32, inner := 512, cols := 8 },
    { rows := 8, inner := 512, cols := 32 } ]

def rowCases : List (String × Shape) :=
  [ ("rows_fixed_cols_64", { rows := 64, inner := 0, cols := 64 }),
    ("rows_fixed_cols_64", { rows := 256, inner := 0, cols := 64 }),
    ("rows_fixed_cols_64", { rows := 1024, inner := 0, cols := 64 }),
    ("rows_fixed_cols_64", { rows := 4096, inner := 0, cols := 64 }),
    ("cols_fixed_rows_64", { rows := 64, inner := 0, cols := 64 }),
    ("cols_fixed_rows_64", { rows := 64, inner := 0, cols := 256 }),
    ("cols_fixed_rows_64", { rows := 64, inner := 0, cols := 1024 }),
    ("cols_fixed_rows_64", { rows := 64, inner := 0, cols := 4096 }) ]

def pivotShapes : List Shape :=
  [ { rows := 128, inner := 0, cols := 128 }, { rows := 512, inner := 0, cols := 64 },
    { rows := 64, inner := 0, cols := 512 }, { rows := 512, inner := 0, cols := 512 } ]

def pivotPatterns : List String := ["first_entry", "late_row", "late_column", "last_entry", "none"]

def rrefCases : List (String × Shape) :=
  [ ("dense_full_rank", { rows := 6, inner := 0, cols := 6 }),
    ("dense_full_rank", { rows := 10, inner := 0, cols := 10 }),
    ("dense_full_rank", { rows := 14, inner := 0, cols := 14 }),
    ("swap_heavy", { rows := 6, inner := 0, cols := 6 }),
    ("swap_heavy", { rows := 10, inner := 0, cols := 10 }),
    ("swap_heavy", { rows := 14, inner := 0, cols := 14 }),
    ("rank_deficient", { rows := 6, inner := 0, cols := 6 }),
    ("rank_deficient", { rows := 10, inner := 0, cols := 10 }),
    ("rank_deficient", { rows := 14, inner := 0, cols := 14 }),
    ("sparse_late_pivot", { rows := 24, inner := 0, cols := 8 }),
    ("sparse_late_pivot", { rows := 8, inner := 0, cols := 24 }),
    ("already_echelon", { rows := 14, inner := 0, cols := 14 }) ]

def controlShapes : List Shape :=
  [ { rows := 64, inner := 0, cols := 64 }, { rows := 256, inner := 0, cols := 256 } ]

def suiteAccess (cfg : BenchConfig) : IO (List BenchSample) :=
  collectCases (selected cfg accessShapes) fun shape => suiteAccessCase cfg shape.rows shape.cols

def suiteConstruction (cfg : BenchConfig) : IO (List BenchSample) :=
  collectCases (selected cfg constructionShapes) fun shape =>
    suiteConstructionCase cfg shape.rows shape.cols

def suiteElementwise (cfg : BenchConfig) : IO (List BenchSample) :=
  collectCases (selected cfg elementwiseShapes) fun shape =>
    suiteElementwiseCase cfg shape.rows shape.cols

def suiteDot (cfg : BenchConfig) : IO (List BenchSample) :=
  collectCases (selected cfg dotDimensions) (suiteDotCase cfg)

def suiteMul (cfg : BenchConfig) : IO (List BenchSample) :=
  collectCases (selected cfg mulShapes) fun shape =>
    suiteMulCase cfg shape.rows shape.inner shape.cols

def suiteRowOps (cfg : BenchConfig) : IO (List BenchSample) :=
  collectCases (selected cfg rowCases) fun item => suiteRowCase cfg item.2.rows item.2.cols item.1

def suitePivot (cfg : BenchConfig) : IO (List BenchSample) := do
  let shapes := selected cfg pivotShapes
  let patterns := selected cfg pivotPatterns
  let mut out : List BenchSample := []
  for shape in shapes do
    for pattern in patterns do
      out := out ++ (← suitePivotCase cfg shape.rows shape.cols pattern)
  return out

def suiteRref (cfg : BenchConfig) : IO (List BenchSample) := do
  let mut out : List BenchSample := []
  for item in selected cfg rrefCases do
    out := out ++ (← suiteRrefCase cfg "ref" item.1 item.2.rows item.2.cols)
    out := out ++ (← suiteRrefCase cfg "rref" item.1 item.2.rows item.2.cols)
  return out

def suiteControls (cfg : BenchConfig) : IO (List BenchSample) :=
  collectCases (selected cfg controlShapes) fun shape => suiteControlCase cfg shape.rows shape.cols

def includeSuite (cfg : BenchConfig) (name : String) : Bool :=
  match cfg.suite with
  | none => true
  | some requested => requested == name

def runAll (cfg : BenchConfig) : IO (List BenchSample) := do
  let mut out : List BenchSample := []
  if includeSuite cfg "access" then
    out := out ++ (← suiteAccess cfg)
  if includeSuite cfg "construction" then
    out := out ++ (← suiteConstruction cfg)
  if includeSuite cfg "elementwise" then
    out := out ++ (← suiteElementwise cfg)
  if includeSuite cfg "dot" then
    out := out ++ (← suiteDot cfg)
  if includeSuite cfg "mul" then
    out := out ++ (← suiteMul cfg)
  if includeSuite cfg "row_ops" then
    out := out ++ (← suiteRowOps cfg)
  if includeSuite cfg "pivot" then
    out := out ++ (← suitePivot cfg)
  if includeSuite cfg "rref" then
    out := out ++ (← suiteRref cfg)
  if includeSuite cfg "control" then
    out := out ++ (← suiteControls cfg)
  return out

def knownSuite (name : String) : Bool :=
  ["access", "construction", "elementwise", "dot", "mul", "row_ops", "pivot", "rref", "control"]
    |>.contains name

def parseNatArgument (flag value : String) : Except String Nat :=
  match value.toNat? with
  | some result => .ok result
  | none => .error s!"{flag} requires a natural number, got {value}"

def parseArgsAux (cfg : BenchConfig) : List String → Except String BenchConfig
  | [] => .ok cfg
  | "--profile" :: value :: rest =>
    if value == "smoke" || value == "full" then
      parseArgsAux { cfg with profile := value } rest
    else
      .error s!"--profile must be smoke or full, got {value}"
  | "--suite" :: value :: rest =>
    if knownSuite value then
      parseArgsAux { cfg with suite := some value } rest
    else
      .error s!"unknown suite {value}"
  | "--seed" :: value :: rest =>
    match parseNatArgument "--seed" value with
    | .ok seed => parseArgsAux { cfg with seed } rest
    | .error message => .error message
  | "--process-run" :: value :: rest =>
    match parseNatArgument "--process-run" value with
    | .ok processRun => parseArgsAux { cfg with processRun } rest
    | .error message => .error message
  | "--jsonl" :: rest => parseArgsAux { cfg with jsonl := true } rest
  | flag :: _ => .error s!"unknown or incomplete argument {flag}"

def parseArgs (args : List String) : Except String BenchConfig :=
  parseArgsAux defaultConfig args

def jsonString (value : String) : String :=
  "\"" ++ value ++ "\""

def jsonLine (sample : BenchSample) : String :=
  "{" ++
    "\"suite\":" ++ jsonString sample.suite ++ "," ++
    "\"operation\":" ++ jsonString sample.operation ++ "," ++
    "\"variant\":" ++ jsonString sample.variantName ++ "," ++
    "\"implementation\":" ++ jsonString sample.implementation ++ "," ++
    "\"coefficient\":" ++ jsonString sample.coefficient ++ "," ++
    "\"pattern\":" ++ jsonString sample.pattern ++ "," ++
    "\"rows\":" ++ toString sample.rows ++ "," ++
    "\"inner\":" ++ toString sample.inner ++ "," ++
    "\"cols\":" ++ toString sample.cols ++ "," ++
    "\"process_run\":" ++ toString sample.processRun ++ "," ++
    "\"sample\":" ++ toString sample.sample ++ "," ++
    "\"batch\":" ++ toString sample.batch ++ "," ++
    "\"nanos\":" ++ toString sample.nanos ++ "," ++
    "\"heartbeats\":" ++ toString sample.heartbeats ++ "," ++
    "\"checksum\":" ++ toString sample.checksum ++ "}"

def humanLine (sample : BenchSample) : String :=
  s!"{sample.suite}/{sample.operation} {sample.variantName}/{sample.implementation}: " ++
    s!"{sample.nanos} ns, {sample.heartbeats} heartbeats, checksum={sample.checksum}"

def main (args : List String) : IO Unit := do
  match parseArgs args with
  | .error message => throw <| IO.userError message
  | .ok cfg =>
    let results ← runAll cfg
    for result in results do
      IO.println (if cfg.jsonl then jsonLine result else humanLine result)

end DenseMatrixBench

def main (args : List String) : IO Unit :=
  DenseMatrixBench.main args
