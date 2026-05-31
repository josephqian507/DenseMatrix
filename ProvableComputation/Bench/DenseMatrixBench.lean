/-
Copyright (c) 2026 Provable Computation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Provable Computation contributors
-/

import ProvableComputation.LinearAlgebra.Determinant.Basic

/-!
# DenseMatrix benchmark support

This module is intentionally outside the core library import surface. It
provides deterministic inputs, checksum helpers, and an IO runner for comparing
compiled DenseMatrix operation runtimes.
-/

namespace DenseMatrixBench

/-
The benchmark harness has to feed the same logical matrices to two different
surfaces: the new Vector-backed `DenseMatrix` code and mathlib's function-backed
`Matrix`.  The small mixers below are deterministic by design, so runs from
different machines can compare JSONL records without carrying input files.
-/
def mixNat (acc x : Nat) : Nat :=
  (acc * 16777619 + x + 1) % 2147483647

def natCode (x : Nat) : Nat :=
  x

def intCode (x : Int) : Nat :=
  x.natAbs * 2 + if x < 0 then 1 else 0

def ratCode (x : Rat) : Nat :=
  mixNat (intCode x.num) x.den

def natEntry (seed i j : Nat) : Nat :=
  ((seed + (i + 1) * 73 + (j + 1) * 193 + i * j * 17) % 997) + 1

def intEntry (seed i j : Nat) : Int :=
  Int.ofNat ((seed + (i + 1) * 97 + (j + 1) * 53 + i * j * 29) % 401) - 200

def ratEntry (seed i j : Nat) : Rat :=
  let den := ((seed + (i + 1) * 31 + (j + 1) * 47) % 37) + 1
  mkRat (intEntry seed i j) den

def bigNatEntry (seed i j : Nat) : Nat :=
  (2 ^ (((seed + i * 3 + j * 5) % 12) + 24)) + natEntry seed i j

def bigIntEntry (seed i j : Nat) : Int :=
  let value := Int.ofNat (bigNatEntry seed i j)
  if (seed + i + j) % 2 = 0 then value else -value

def bigRatEntry (seed i j : Nat) : Rat :=
  let den := ((seed + (i + 1) * 11 + (j + 1) * 13) % 9) + 1
  mkRat (bigIntEntry seed i j) den

/-
Each constructor family is duplicated for `Matrix` and `DenseMatrix` so the
benchmarks can separate representation cost from operation cost.  The entry
functions are shared, which keeps the DenseMatrix/mathlib comparisons about the
backend rather than about different test data.
-/
def matrixNat (m n seed : Nat) : Matrix (Fin m) (Fin n) Nat :=
  Matrix.of fun i j => natEntry seed i.val j.val

def matrixInt (m n seed : Nat) : Matrix (Fin m) (Fin n) Int :=
  Matrix.of fun i j => intEntry seed i.val j.val

def matrixRat (m n seed : Nat) : Matrix (Fin m) (Fin n) Rat :=
  Matrix.of fun i j => ratEntry seed i.val j.val

def matrixNatZero (m n : Nat) : Matrix (Fin m) (Fin n) Nat :=
  Matrix.of fun _ _ => 0

def matrixIntZero (m n : Nat) : Matrix (Fin m) (Fin n) Int :=
  Matrix.of fun _ _ => 0

def matrixNatIdentity (n : Nat) : Matrix (Fin n) (Fin n) Nat :=
  Matrix.of fun i j => if i.val = j.val then 1 else 0

def matrixNatBig (m n seed : Nat) : Matrix (Fin m) (Fin n) Nat :=
  Matrix.of fun i j => bigNatEntry seed i.val j.val

def matrixIntBig (m n seed : Nat) : Matrix (Fin m) (Fin n) Int :=
  Matrix.of fun i j => bigIntEntry seed i.val j.val

def matrixRatBig (m n seed : Nat) : Matrix (Fin m) (Fin n) Rat :=
  Matrix.of fun i j => bigRatEntry seed i.val j.val

def denseNat (m n seed : Nat) : DenseMatrix m n Nat :=
  DenseMatrix.of fun i j => natEntry seed i.val j.val

def denseInt (m n seed : Nat) : DenseMatrix m n Int :=
  DenseMatrix.of fun i j => intEntry seed i.val j.val

def denseRat (m n seed : Nat) : DenseMatrix m n Rat :=
  DenseMatrix.of fun i j => ratEntry seed i.val j.val

def denseNatZero (m n : Nat) : DenseMatrix m n Nat :=
  DenseMatrix.of fun _ _ => 0

def denseIntZero (m n : Nat) : DenseMatrix m n Int :=
  DenseMatrix.of fun _ _ => 0

def denseNatIdentity (n : Nat) : DenseMatrix n n Nat :=
  DenseMatrix.of fun i j => if i.val = j.val then 1 else 0

def denseNatBig (m n seed : Nat) : DenseMatrix m n Nat :=
  DenseMatrix.of fun i j => bigNatEntry seed i.val j.val

def denseIntBig (m n seed : Nat) : DenseMatrix m n Int :=
  DenseMatrix.of fun i j => bigIntEntry seed i.val j.val

def denseRatBig (m n seed : Nat) : DenseMatrix m n Rat :=
  DenseMatrix.of fun i j => bigRatEntry seed i.val j.val

/-
Benchmarks return stable checksums instead of large matrices.  This both forces
the pure computation before the timer stops and preserves a cheap correctness
signal in every JSONL record, including the row-operation logs used by REF/RREF
and LU.
-/
def checksumDenseUnchecked {m n : Nat} {α : Type} [Inhabited α]
    (encode : α → Nat) (A : DenseMatrix m n α) : Nat :=
  Id.run do
    let mut acc := 2166136261
    for i in [0:m] do
      for j in [0:n] do
        acc := mixNat acc (encode (A.get! i j))
    return acc

def checksumDenseChecked {m n : Nat} {α : Type}
    (encode : α → Nat) (A : DenseMatrix m n α) : Nat :=
  Id.run do
    let mut acc := 2166136261
    for i in List.finRange m do
      for j in List.finRange n do
        acc := mixNat acc (encode (A.get i j))
    return acc

def checksumMatrix {m n : Nat} {α : Type}
    (encode : α → Nat) (A : Matrix (Fin m) (Fin n) α) : Nat :=
  Id.run do
    let mut acc := 2166136261
    for i in List.finRange m do
      for j in List.finRange n do
        acc := mixNat acc (encode (A i j))
    return acc

def rowOpRatCode {n : Nat} : RowOp n Rat → Nat
  | .swap i j => mixNat (mixNat 101 i.val) j.val
  | .factor i c => mixNat (mixNat 211 i.val) (ratCode c)
  | .replace use toReplace k => mixNat (mixNat (mixNat 307 use.val) toReplace.val) (ratCode k)

def checksumRowOpsRat {n : Nat} (steps : List (RowOp n Rat)) : Nat :=
  steps.foldl (fun acc op => mixNat acc (rowOpRatCode op)) 2166136261

def checksumRowReductionRat {m n : Nat} (result : DenseMatrix.RowReductionResult m n Rat) :
    Nat :=
  mixNat (checksumDenseUnchecked ratCode result.matrix) (checksumRowOpsRat result.steps)

def checksumLURat {m n : Nat} (lu : DenseMatrix.LUFactors m n Rat) : Nat :=
  mixNat
    (mixNat (checksumDenseUnchecked ratCode lu.P) (checksumDenseUnchecked ratCode lu.L))
    (checksumDenseUnchecked ratCode lu.U)

/-
Square DenseMatrix kernels allocate their inputs inside the timed action.  These
cases represent the public API cost a caller pays when constructing data and
immediately running a primitive operation or a higher-level elimination routine.
-/
def runOfNat (n : Nat) : Nat :=
  checksumDenseUnchecked natCode (denseNat n n 11)

def runOfMatrixNat (n : Nat) : Nat :=
  checksumDenseUnchecked natCode (DenseMatrix.ofMatrix (matrixNat n n 13))

def runToMatrixNat (n : Nat) : Nat :=
  checksumMatrix natCode (DenseMatrix.toMatrix (denseNat n n 17))

def runGetCheckedNat (n : Nat) : Nat :=
  checksumDenseChecked natCode (denseNat n n 19)

def runGetUncheckedNat (n : Nat) : Nat :=
  checksumDenseUnchecked natCode (denseNat n n 23)

def runSetCheckedNat (n : Nat) : Nat :=
  let A := denseNat n n 29
  let B := Id.run do
    let mut B := A
    for i in List.finRange n do
      for j in List.finRange n do
        B := B.set i j (natEntry 31 i.val j.val)
    return B
  checksumDenseUnchecked natCode B

def runSetUncheckedNat (n : Nat) : Nat :=
  let A := denseNat n n 37
  let B := Id.run do
    let mut B := A
    for i in [0:n] do
      for j in [0:n] do
        B := B.set! i j (natEntry 41 i j)
    return B
  checksumDenseUnchecked natCode B

def runAddInt (n : Nat) : Nat :=
  checksumDenseUnchecked intCode (DenseMatrix.add (denseInt n n 43) (denseInt n n 47))

def runSmulInt (n : Nat) : Nat :=
  checksumDenseUnchecked intCode (DenseMatrix.smul (-7 : Int) (denseInt n n 53))

def runTransposeInt (n : Nat) : Nat :=
  if hn : n = 0 then
    0
  else
    haveI : NeZero n := ⟨hn⟩
    checksumDenseUnchecked intCode (DenseMatrix.transpose (denseInt n n 59))

def runMulSquareNat (n : Nat) : Nat :=
  if hn : n = 0 then
    0
  else
    haveI : NeZero n := ⟨hn⟩
    checksumDenseUnchecked natCode (DenseMatrix.mul (denseNat n n 61) (denseNat n n 67))

def runMulRectInt (n : Nat) : Nat :=
  if hn : n = 0 then
    0
  else
    haveI : NeZero n := ⟨hn⟩
    haveI : NeZero (n + 1) := ⟨by simp⟩
    haveI : NeZero (n + 2) := ⟨by simp⟩
    checksumDenseUnchecked intCode
      (DenseMatrix.mul (m := n) (k := n + 1) (n := n + 2)
        (denseInt n (n + 1) 71) (denseInt (n + 1) (n + 2) 73))

def runAddRat (n : Nat) : Nat :=
  checksumDenseUnchecked ratCode (DenseMatrix.add (denseRat n n 79) (denseRat n n 83))

def runMulSquareRat (n : Nat) : Nat :=
  if hn : n = 0 then
    0
  else
    haveI : NeZero n := ⟨hn⟩
    checksumDenseUnchecked ratCode (DenseMatrix.mul (denseRat n n 89) (denseRat n n 97))

def runRowEchelonFormRat (n : Nat) : Nat :=
  checksumRowReductionRat (DenseMatrix.rowEchelonForm (denseRat n n 157))

def runReducedRowEchelonFormRat (n : Nat) : Nat :=
  checksumRowReductionRat (DenseMatrix.reducedRowEchelonForm (denseRat n n 163))

def runLUFactorizationRat (n : Nat) : Nat :=
  checksumLURat (DenseMatrix.luFactorization (denseRat n n 167))

def runGaussDetRat (n : Nat) : Nat :=
  ratCode (DenseMatrix.gaussDet (denseRat n n 173))

def runLUDetRat (n : Nat) : Nat :=
  ratCode (DenseMatrix.luDet (denseRat n n 173))

/-
Elementary row and column operations need nonempty dimensions to choose the
fixed `Fin.ofNat` rows and columns used below.  Returning `0` for degenerate
shapes keeps the benchmark scheduler total while still exercising zero-row and
zero-column construction elsewhere.
-/
def runSwapRowRatDims (m n : Nat) : Nat :=
  if hm : m = 0 then
    0
  else
    haveI : NeZero m := ⟨hm⟩
    checksumDenseUnchecked ratCode
      (DenseMatrix.swapRow (denseRat m n 271) (Fin.ofNat m 0) (Fin.ofNat m 1))

def runFactorRatDims (m n : Nat) : Nat :=
  if hm : m = 0 then
    0
  else
    haveI : NeZero m := ⟨hm⟩
    checksumDenseUnchecked ratCode
      (DenseMatrix.factor (denseRat m n 277) (Fin.ofNat m 1) (mkRat 3 2))

def runReplaceRatDims (m n : Nat) : Nat :=
  if hm : m = 0 then
    0
  else
    haveI : NeZero m := ⟨hm⟩
    checksumDenseUnchecked ratCode
      (DenseMatrix.replace (denseRat m n 281) (Fin.ofNat m 0) (Fin.ofNat m 1) (mkRat (-2) 3))

def runSwapColRatDims (m n : Nat) : Nat :=
  if hn : n = 0 then
    0
  else
    haveI : NeZero n := ⟨hn⟩
    checksumDenseUnchecked ratCode
      (DenseMatrix.swapCol (denseRat m n 283) (Fin.ofNat n 0) (Fin.ofNat n 1))

def runFactorColRatDims (m n : Nat) : Nat :=
  if hn : n = 0 then
    0
  else
    haveI : NeZero n := ⟨hn⟩
    checksumDenseUnchecked ratCode
      (DenseMatrix.factorCol (denseRat m n 293) (Fin.ofNat n 1) (mkRat 5 3))

def runReplaceColRatDims (m n : Nat) : Nat :=
  if hn : n = 0 then
    0
  else
    haveI : NeZero n := ⟨hn⟩
    checksumDenseUnchecked ratCode
      (DenseMatrix.replaceCol (denseRat m n 307) (Fin.ofNat n 0) (Fin.ofNat n 1)
        (mkRat (-3) 4))

def runToStringNat (n : Nat) : Nat :=
  (toString (denseNat n n 101)).length

/-
Data-profile kernels hold the shape constant while changing values.  Zero,
identity, and large-magnitude inputs catch behavior that pure random-ish dense
matrices hide, especially multiplication shortcuts and rational/integer size
growth.
-/
def runAddIntZero (n : Nat) : Nat :=
  checksumDenseUnchecked intCode (DenseMatrix.add (denseIntZero n n) (denseIntZero n n))

def runMulSquareNatZero (n : Nat) : Nat :=
  if hn : n = 0 then
    0
  else
    haveI : NeZero n := ⟨hn⟩
    checksumDenseUnchecked natCode (DenseMatrix.mul (denseNatZero n n) (denseNatZero n n))

def runMulSquareNatIdentity (n : Nat) : Nat :=
  if hn : n = 0 then
    0
  else
    haveI : NeZero n := ⟨hn⟩
    checksumDenseUnchecked natCode (DenseMatrix.mul (denseNatIdentity n) (denseNatIdentity n))

def runMulSquareNatBig (n : Nat) : Nat :=
  if hn : n = 0 then
    0
  else
    haveI : NeZero n := ⟨hn⟩
    checksumDenseUnchecked natCode (DenseMatrix.mul (denseNatBig n n 103) (denseNatBig n n 107))

def runAddIntBig (n : Nat) : Nat :=
  checksumDenseUnchecked intCode (DenseMatrix.add (denseIntBig n n 109) (denseIntBig n n 113))

def runMulSquareIntBig (n : Nat) : Nat :=
  if hn : n = 0 then
    0
  else
    haveI : NeZero n := ⟨hn⟩
    checksumDenseUnchecked intCode (DenseMatrix.mul (denseIntBig n n 127) (denseIntBig n n 131))

def runAddRatBig (n : Nat) : Nat :=
  checksumDenseUnchecked ratCode (DenseMatrix.add (denseRatBig n n 137) (denseRatBig n n 139))

def runMulSquareRatBig (n : Nat) : Nat :=
  if hn : n = 0 then
    0
  else
    haveI : NeZero n := ⟨hn⟩
    checksumDenseUnchecked ratCode (DenseMatrix.mul (denseRatBig n n 149) (denseRatBig n n 151))

/-
Rectangular kernels use explicit `(m, n)` or `(m, k, n)` dimensions.  They
exercise the same DenseMatrix operations as the square suite, but make sure the
row-major helpers are not accidentally relying on square arithmetic.
-/
def runOfNatDims (m n : Nat) : Nat :=
  checksumDenseUnchecked natCode (denseNat m n 171)

def runOfMatrixNatDims (m n : Nat) : Nat :=
  checksumDenseUnchecked natCode (DenseMatrix.ofMatrix (matrixNat m n 173))

def runToMatrixNatDims (m n : Nat) : Nat :=
  checksumMatrix natCode (DenseMatrix.toMatrix (denseNat m n 179))

def runGetCheckedNatDims (m n : Nat) : Nat :=
  checksumDenseChecked natCode (denseNat m n 181)

def runGetUncheckedNatDims (m n : Nat) : Nat :=
  checksumDenseUnchecked natCode (denseNat m n 191)

def runSetCheckedNatDims (m n : Nat) : Nat :=
  let A := denseNat m n 193
  let B := Id.run do
    let mut B := A
    for i in List.finRange m do
      for j in List.finRange n do
        B := B.set i j (natEntry 197 i.val j.val)
    return B
  checksumDenseUnchecked natCode B

def runSetUncheckedNatDims (m n : Nat) : Nat :=
  let A := denseNat m n 199
  let B := Id.run do
    let mut B := A
    for i in [0:m] do
      for j in [0:n] do
        B := B.set! i j (natEntry 211 i j)
    return B
  checksumDenseUnchecked natCode B

def runSetCheckedNatFrom {m n : Nat} (A : DenseMatrix m n Nat) (seed : Nat) : Nat :=
  let B := Id.run do
    let mut B := A
    for i in List.finRange m do
      for j in List.finRange n do
        B := B.set i j (natEntry seed i.val j.val)
    return B
  checksumDenseUnchecked natCode B

def runSetUncheckedNatFrom {m n : Nat} (A : DenseMatrix m n Nat) (seed : Nat) : Nat :=
  let B := Id.run do
    let mut B := A
    for i in [0:m] do
      for j in [0:n] do
        B := B.set! i j (natEntry seed i j)
    return B
  checksumDenseUnchecked natCode B

def runTransposeIntFrom {m n : Nat} (A : DenseMatrix m n Int) : Nat :=
  if hm : m = 0 then
    0
  else if hn : n = 0 then
    0
  else
    haveI : NeZero m := ⟨hm⟩
    haveI : NeZero n := ⟨hn⟩
    checksumDenseUnchecked intCode (DenseMatrix.transpose A)

def runMulNatFrom {m k n : Nat} (A : DenseMatrix m k Nat) (B : DenseMatrix k n Nat) : Nat :=
  if hm : m = 0 then
    0
  else if hk : k = 0 then
    0
  else if hn : n = 0 then
    0
  else
    haveI : NeZero m := ⟨hm⟩
    haveI : NeZero k := ⟨hk⟩
    haveI : NeZero n := ⟨hn⟩
    checksumDenseUnchecked natCode (DenseMatrix.mul A B)

def runMulIntFrom {m k n : Nat} (A : DenseMatrix m k Int) (B : DenseMatrix k n Int) : Nat :=
  if hm : m = 0 then
    0
  else if hk : k = 0 then
    0
  else if hn : n = 0 then
    0
  else
    haveI : NeZero m := ⟨hm⟩
    haveI : NeZero k := ⟨hk⟩
    haveI : NeZero n := ⟨hn⟩
    checksumDenseUnchecked intCode (DenseMatrix.mul A B)

def runMulRatFrom {m k n : Nat} (A : DenseMatrix m k Rat) (B : DenseMatrix k n Rat) : Nat :=
  if hm : m = 0 then
    0
  else if hk : k = 0 then
    0
  else if hn : n = 0 then
    0
  else
    haveI : NeZero m := ⟨hm⟩
    haveI : NeZero k := ⟨hk⟩
    haveI : NeZero n := ⟨hn⟩
    checksumDenseUnchecked ratCode (DenseMatrix.mul A B)

def runRowEchelonFormRatFrom {n : Nat} (A : DenseMatrix n n Rat) : Nat :=
  checksumRowReductionRat (DenseMatrix.rowEchelonForm A)

def runReducedRowEchelonFormRatFrom {n : Nat} (A : DenseMatrix n n Rat) : Nat :=
  checksumRowReductionRat (DenseMatrix.reducedRowEchelonForm A)

def runLUFactorizationRatFrom {n : Nat} (A : DenseMatrix n n Rat) : Nat :=
  checksumLURat (DenseMatrix.luFactorization A)

def runGaussDetRatFrom {n : Nat} (A : DenseMatrix n n Rat) : Nat :=
  ratCode (DenseMatrix.gaussDet A)

def runLUDetRatFrom {n : Nat} (A : DenseMatrix n n Rat) : Nat :=
  ratCode (DenseMatrix.luDet A)

def runSwapRowRatFrom {m n : Nat} (A : DenseMatrix m n Rat) : Nat :=
  if hm : m = 0 then
    0
  else
    haveI : NeZero m := ⟨hm⟩
    checksumDenseUnchecked ratCode (DenseMatrix.swapRow A (Fin.ofNat m 0) (Fin.ofNat m 1))

def runFactorRatFrom {m n : Nat} (A : DenseMatrix m n Rat) : Nat :=
  if hm : m = 0 then
    0
  else
    haveI : NeZero m := ⟨hm⟩
    checksumDenseUnchecked ratCode (DenseMatrix.factor A (Fin.ofNat m 1) (mkRat 3 2))

def runReplaceRatFrom {m n : Nat} (A : DenseMatrix m n Rat) : Nat :=
  if hm : m = 0 then
    0
  else
    haveI : NeZero m := ⟨hm⟩
    checksumDenseUnchecked ratCode
      (DenseMatrix.replace A (Fin.ofNat m 0) (Fin.ofNat m 1) (mkRat (-2) 3))

def runSwapColRatFrom {m n : Nat} (A : DenseMatrix m n Rat) : Nat :=
  if hn : n = 0 then
    0
  else
    haveI : NeZero n := ⟨hn⟩
    checksumDenseUnchecked ratCode (DenseMatrix.swapCol A (Fin.ofNat n 0) (Fin.ofNat n 1))

def runFactorColRatFrom {m n : Nat} (A : DenseMatrix m n Rat) : Nat :=
  if hn : n = 0 then
    0
  else
    haveI : NeZero n := ⟨hn⟩
    checksumDenseUnchecked ratCode (DenseMatrix.factorCol A (Fin.ofNat n 1) (mkRat 5 3))

def runReplaceColRatFrom {m n : Nat} (A : DenseMatrix m n Rat) : Nat :=
  if hn : n = 0 then
    0
  else
    haveI : NeZero n := ⟨hn⟩
    checksumDenseUnchecked ratCode
      (DenseMatrix.replaceCol A (Fin.ofNat n 0) (Fin.ofNat n 1) (mkRat (-3) 4))

def runAddIntDims (m n : Nat) : Nat :=
  checksumDenseUnchecked intCode (DenseMatrix.add (denseInt m n 223) (denseInt m n 227))

def runSmulIntDims (m n : Nat) : Nat :=
  checksumDenseUnchecked intCode (DenseMatrix.smul (-7 : Int) (denseInt m n 229))

def runTransposeIntDims (m n : Nat) : Nat :=
  if hm : m = 0 then
    0
  else if hn : n = 0 then
    0
  else
    haveI : NeZero m := ⟨hm⟩
    haveI : NeZero n := ⟨hn⟩
    checksumDenseUnchecked intCode (DenseMatrix.transpose (denseInt m n 233))

def runMulNatDims (m k n : Nat) : Nat :=
  if hm : m = 0 then
    0
  else if hk : k = 0 then
    0
  else if hn : n = 0 then
    0
  else
    haveI : NeZero m := ⟨hm⟩
    haveI : NeZero k := ⟨hk⟩
    haveI : NeZero n := ⟨hn⟩
    checksumDenseUnchecked natCode
      (DenseMatrix.mul (m := m) (k := k) (n := n)
        (denseNat m k 239) (denseNat k n 241))

def runMulIntDims (m k n : Nat) : Nat :=
  if hm : m = 0 then
    0
  else if hk : k = 0 then
    0
  else if hn : n = 0 then
    0
  else
    haveI : NeZero m := ⟨hm⟩
    haveI : NeZero k := ⟨hk⟩
    haveI : NeZero n := ⟨hn⟩
    checksumDenseUnchecked intCode
      (DenseMatrix.mul (m := m) (k := k) (n := n)
        (denseInt m k 251) (denseInt k n 257))

/-
The mathlib reference kernels mirror the DenseMatrix cases above.  They provide
the comparison track in the same executable so compiler flags, Lean version, and
machine state are shared between the two representations.
-/
def runToStringNatDims (m n : Nat) : Nat :=
  (toString (denseNat m n 263)).length

def runMatrixConstructNat (n : Nat) : Nat :=
  checksumMatrix natCode (matrixNat n n 11)

def runMatrixGetNat (n : Nat) : Nat :=
  checksumMatrix natCode (matrixNat n n 19)

def runMatrixAddInt (n : Nat) : Nat :=
  checksumMatrix intCode (matrixInt n n 43 + matrixInt n n 47)

def runMatrixSmulInt (n : Nat) : Nat :=
  checksumMatrix intCode (Matrix.of fun i j => (-7 : Int) * matrixInt n n 53 i j)

def runMatrixTransposeInt (n : Nat) : Nat :=
  checksumMatrix intCode ((matrixInt n n 59).transpose)

def runMatrixMulSquareNat (n : Nat) : Nat :=
  checksumMatrix natCode (matrixNat n n 61 * matrixNat n n 67)

def runMatrixMulRectInt (n : Nat) : Nat :=
  checksumMatrix intCode
    (matrixInt n (n + 1) 71 * matrixInt (n + 1) (n + 2) 73)

def runMatrixAddRat (n : Nat) : Nat :=
  checksumMatrix ratCode (matrixRat n n 79 + matrixRat n n 83)

def runMatrixMulSquareRat (n : Nat) : Nat :=
  checksumMatrix ratCode (matrixRat n n 89 * matrixRat n n 97)

def runMatrixAddIntZero (n : Nat) : Nat :=
  checksumMatrix intCode (matrixIntZero n n + matrixIntZero n n)

def runMatrixMulSquareNatZero (n : Nat) : Nat :=
  checksumMatrix natCode (matrixNatZero n n * matrixNatZero n n)

def runMatrixMulSquareNatIdentity (n : Nat) : Nat :=
  checksumMatrix natCode (matrixNatIdentity n * matrixNatIdentity n)

def runMatrixMulSquareNatBig (n : Nat) : Nat :=
  checksumMatrix natCode (matrixNatBig n n 103 * matrixNatBig n n 107)

def runMatrixAddIntBig (n : Nat) : Nat :=
  checksumMatrix intCode (matrixIntBig n n 109 + matrixIntBig n n 113)

def runMatrixMulSquareIntBig (n : Nat) : Nat :=
  checksumMatrix intCode (matrixIntBig n n 127 * matrixIntBig n n 131)

def runMatrixAddRatBig (n : Nat) : Nat :=
  checksumMatrix ratCode (matrixRatBig n n 137 + matrixRatBig n n 139)

def runMatrixMulSquareRatBig (n : Nat) : Nat :=
  checksumMatrix ratCode (matrixRatBig n n 149 * matrixRatBig n n 151)

def runMatrixConstructNatDims (m n : Nat) : Nat :=
  checksumMatrix natCode (matrixNat m n 171)

def runMatrixGetNatDims (m n : Nat) : Nat :=
  checksumMatrix natCode (matrixNat m n 181)

def runMatrixAddIntDims (m n : Nat) : Nat :=
  checksumMatrix intCode (matrixInt m n 223 + matrixInt m n 227)

def runMatrixSmulIntDims (m n : Nat) : Nat :=
  checksumMatrix intCode (Matrix.of fun i j => (-7 : Int) * matrixInt m n 229 i j)

def runMatrixTransposeIntDims (m n : Nat) : Nat :=
  checksumMatrix intCode ((matrixInt m n 233).transpose)

def runMatrixMulNatDims (m k n : Nat) : Nat :=
  checksumMatrix natCode (matrixNat m k 239 * matrixNat k n 241)

def runMatrixMulIntDims (m k n : Nat) : Nat :=
  checksumMatrix intCode (matrixInt m k 251 * matrixInt k n 257)

/-- Summary statistics emitted for each benchmark row in the JSONL stream. -/
structure Stats where
  count : Nat
  minMs : Float
  q1Ms : Float
  medianMs : Float
  meanMs : Float
  p90Ms : Float
  p95Ms : Float
  q3Ms : Float
  maxMs : Float
  stddevMs : Float
  madMs : Float
  cv : Float

/-
The summary keeps raw samples in the output, but also precomputes the percentiles
and dispersion measures used by the shell-side suite reports.  It intentionally
does not discard outliers; benchmark comparison scripts can choose their own
policy from the recorded sample array.
-/
def summarize (samples : Array Nat) : Stats :=
  if samples.isEmpty then
    { count := 0
      minMs := 0.0
      q1Ms := 0.0
      medianMs := 0.0
      meanMs := 0.0
      p90Ms := 0.0
      p95Ms := 0.0
      q3Ms := 0.0
      maxMs := 0.0
      stddevMs := 0.0
      madMs := 0.0
      cv := 0.0 }
  else
    let ms := samples.map fun n => n.toFloat / 1000000.0
    let sorted := ms.qsort (fun a b => a < b)
    let count := samples.size
    let percentileIndex (pct : Nat) : Nat :=
      let idx := (count * pct) / 100
      if idx < count then idx else count - 1
    let sum := ms.foldl (fun acc x => acc + x) 0.0
    let mean := sum / count.toFloat
    let median := sorted[count / 2]!
    let absDev := ms.map fun x => if x < median then median - x else x - median
    let sortedAbsDev := absDev.qsort (fun a b => a < b)
    let variance := ms.foldl (fun acc x =>
      let delta := x - mean
      acc + delta * delta) 0.0 / count.toFloat
    let stddev := Float.sqrt variance
    { count := count
      minMs := sorted[0]!
      q1Ms := sorted[percentileIndex 25]!
      medianMs := median
      meanMs := mean
      p90Ms := sorted[percentileIndex 90]!
      p95Ms := sorted[percentileIndex 95]!
      q3Ms := sorted[percentileIndex 75]!
      maxMs := sorted[count - 1]!
      stddevMs := stddev
      madMs := sortedAbsDev[count / 2]!
      cv := if mean == 0.0 then 0.0 else stddev / mean }

/-- Runtime configuration parsed from `lake exe densematrix_bench` arguments. -/
structure Config where
  quick : Bool := false
  repeatsOpt : Option Nat := none
  warmupsOpt : Option Nat := none
  sizesOpt : Option (List Nat) := none
  ratMaxOpt : Option Nat := none
  stringMaxOpt : Option Nat := none
  dataMaxOpt : Option Nat := none
  jsonl : Option String := none
  showHelp : Bool := false

/-
Configuration normalization centralizes the suite defaults.  Keeping the limits
for Rat, string formatting, and data-profile cases separate lets the full suite
cover expensive correctness-sensitive operations without making every large
shape pay the same cost.
-/
def defaultSizes (quick : Bool) : List Nat :=
  if quick then [0, 1, 2, 3, 4] else [0, 1, 2, 3, 4, 8, 16, 32, 64, 96, 128]

def effectiveRepeats (cfg : Config) : Nat :=
  cfg.repeatsOpt.getD (if cfg.quick then 3 else 30)

def effectiveWarmups (cfg : Config) : Nat :=
  cfg.warmupsOpt.getD (if cfg.quick then 1 else 5)

def effectiveSizes (cfg : Config) : List Nat :=
  cfg.sizesOpt.getD (defaultSizes cfg.quick)

def effectiveRatMax (cfg : Config) : Nat :=
  cfg.ratMaxOpt.getD (if cfg.quick then 4 else 16)

def effectiveStringMax (cfg : Config) : Nat :=
  cfg.stringMaxOpt.getD (if cfg.quick then 4 else 16)

def effectiveDataMax (cfg : Config) : Nat :=
  cfg.dataMaxOpt.getD (if cfg.quick then 4 else 16)

/-
The runner stays self-contained and avoids bringing in an argument-parsing
dependency.  The accepted flags match the shell benchmark suite, so the Lean
executable remains usable both directly and through the reboot-friendly scripts.
-/
def trimString (s : String) : String :=
  s.trimAscii.toString

def parseNatArg (flag value : String) : Except String Nat :=
  match (trimString value).toNat? with
  | some n => .ok n
  | none => .error s!"{flag} expects a natural number, got '{value}'"

def parseNatList (value : String) : Except String (List Nat) :=
  let parts := value.splitOn ","
  let rec go : List String → List Nat → Except String (List Nat)
    | [], acc => .ok acc.reverse
    | part :: rest, acc =>
        let trimmed := trimString part
        if trimmed.isEmpty then
          .error s!"--sizes contains an empty entry: '{value}'"
        else
          match trimmed.toNat? with
          | some n => go rest (n :: acc)
          | none => .error s!"--sizes expects comma-separated natural numbers, got '{part}'"
  go parts []

partial def parseArgsAux : List String → Config → Except String Config
  | [], cfg => .ok cfg
  | "--help" :: _, cfg => .ok { cfg with showHelp := true }
  | "-h" :: _, cfg => .ok { cfg with showHelp := true }
  | "--quick" :: rest, cfg => parseArgsAux rest { cfg with quick := true }
  | "--repeats" :: value :: rest, cfg => do
      parseArgsAux rest { cfg with repeatsOpt := some (← parseNatArg "--repeats" value) }
  | "--repeats" :: [], _ => .error "--repeats requires a value"
  | "--warmups" :: value :: rest, cfg => do
      parseArgsAux rest { cfg with warmupsOpt := some (← parseNatArg "--warmups" value) }
  | "--warmups" :: [], _ => .error "--warmups requires a value"
  | "--sizes" :: value :: rest, cfg => do
      parseArgsAux rest { cfg with sizesOpt := some (← parseNatList value) }
  | "--sizes" :: [], _ => .error "--sizes requires a comma-separated value"
  | "--rat-max" :: value :: rest, cfg => do
      parseArgsAux rest { cfg with ratMaxOpt := some (← parseNatArg "--rat-max" value) }
  | "--rat-max" :: [], _ => .error "--rat-max requires a value"
  | "--string-max" :: value :: rest, cfg => do
      parseArgsAux rest { cfg with stringMaxOpt := some (← parseNatArg "--string-max" value) }
  | "--string-max" :: [], _ => .error "--string-max requires a value"
  | "--data-max" :: value :: rest, cfg => do
      parseArgsAux rest { cfg with dataMaxOpt := some (← parseNatArg "--data-max" value) }
  | "--data-max" :: [], _ => .error "--data-max requires a value"
  | "--jsonl" :: value :: rest, cfg =>
      parseArgsAux rest { cfg with jsonl := some value }
  | "--jsonl" :: [], _ => .error "--jsonl requires a path or '-'"
  | arg :: _, _ => .error s!"unknown argument '{arg}'"

def parseArgs (args : List String) : Except String Config :=
  parseArgsAux args {}

def usage : String :=
  String.intercalate "\n" [
    "Usage: lake exe densematrix_bench [options]",
    "",
    "Options:",
    "  --quick              Use small sizes and short repeats.",
    "  --repeats N          Number of measured repeats.",
    "  --warmups N          Number of warmup runs.",
    "  --sizes A,B,C        Base sizes; full default is 0,1,2,3,4..128.",
    "  --rat-max N          Only run Rat cases for sizes <= N; full default is 16.",
    "  --string-max N       Only run DenseMatrix.toString cases for sizes <= N.",
    "  --data-max N         Only run extra data-profile cases for sizes <= N.",
    "  --jsonl PATH         Write JSONL output to PATH; '-' means stdout.",
    "  --help               Show this help."
  ]

/-
Every measured case is one JSON object.  The schema names the track
(`compiler_dense`, `compiler_mathlib`, or prebuilt variants), operation,
element type, shape, timing samples, and checksum so later scripts can aggregate
without re-running Lean.
-/
def jsonNatArray (xs : Array Nat) : String :=
  "[" ++ String.intercalate "," (xs.toList.map fun x => toString x) ++ "]"

def jsonLine (track operation element dataProfile : String)
    (rows cols inner warmups repeats checksum : Nat) (samples : Array Nat) (stats : Stats) :
    String :=
  "{" ++
  s!"\"track\":\"{track}\"," ++
  s!"\"operation\":\"{operation}\"," ++
  s!"\"element\":\"{element}\"," ++
  s!"\"data_profile\":\"{dataProfile}\"," ++
  s!"\"rows\":{rows}," ++
  s!"\"cols\":{cols}," ++
  s!"\"inner\":{inner}," ++
  s!"\"warmups\":{warmups}," ++
  s!"\"repeats\":{repeats}," ++
  s!"\"checksum\":{checksum}," ++
  s!"\"duration_unit\":\"ms\"," ++
  s!"\"count\":{stats.count}," ++
  s!"\"samples_unit\":\"ns\"," ++
  s!"\"samples_ns\":{jsonNatArray samples}," ++
  s!"\"min_ms\":{stats.minMs}," ++
  s!"\"q1_ms\":{stats.q1Ms}," ++
  s!"\"median_ms\":{stats.medianMs}," ++
  s!"\"mean_ms\":{stats.meanMs}," ++
  s!"\"p90_ms\":{stats.p90Ms}," ++
  s!"\"p95_ms\":{stats.p95Ms}," ++
  s!"\"q3_ms\":{stats.q3Ms}," ++
  s!"\"max_ms\":{stats.maxMs}," ++
  s!"\"stddev_ms\":{stats.stddevMs}," ++
  s!"\"mad_ms\":{stats.madMs}," ++
  s!"\"cv\":{stats.cv}" ++
  "}"

@[noinline]
def forceNatForTiming (x : Nat) : IO Unit := do
  -- The branch forces `x` before the timer stops; without this guard the
  -- compiler can leave large pure results to be demanded by checksum folding.
  if x == 0 then
    IO.sleep 0
  else
    pure ()

def measurePureProfile (cfg : Config) (dataProfile track operation element : String)
    (rows cols inner : Nat) (action : Unit → Nat) : IO String := do
  let warmups := effectiveWarmups cfg
  let repeats := effectiveRepeats cfg
  for _ in [0:warmups] do
    forceNatForTiming (mixNat 0 (action ()))
  let mut samples : Array Nat := #[]
  let mut checksum := 0
  for _ in [0:repeats] do
    let start ← IO.monoNanosNow
    let nextChecksum := mixNat checksum (action ())
    forceNatForTiming nextChecksum
    let stop ← IO.monoNanosNow
    checksum := nextChecksum
    samples := samples.push (stop - start)
  return jsonLine track operation element dataProfile rows cols inner warmups repeats checksum
    samples (summarize samples)

def measurePure (cfg : Config) (track operation element : String) (rows cols inner : Nat)
    (action : Unit → Nat) : IO String :=
  measurePureProfile cfg "deterministic" track operation element rows cols inner action

/-
The appenders below encode the benchmark taxonomy.  A caller passes the current
JSONL accumulator, and each appender adds a coherent group: elementary
row/column operations, rectangular shape coverage, multiplication shapes, or
prebuilt-input variants that remove construction from the timed region.
-/
def elementaryName (op label : String) : String :=
  if label = "" then op else s!"{op}_{label}"

def appendElementaryShapeBenchmarks (cfg : Config) (lines : Array String) (label : String)
    (m n : Nat) : IO (Array String) := do
  let mut lines := lines
  lines := lines.push
    (← measurePure cfg "compiler_dense" (elementaryName "swapRow" label) "Rat" m n 0
      (fun _ => runSwapRowRatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_dense" (elementaryName "factor" label) "Rat" m n 0
      (fun _ => runFactorRatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_dense" (elementaryName "replace" label) "Rat" m n 0
      (fun _ => runReplaceRatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_dense" (elementaryName "swapCol" label) "Rat" m n 0
      (fun _ => runSwapColRatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_dense" (elementaryName "factorCol" label) "Rat" m n 0
      (fun _ => runFactorColRatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_dense" (elementaryName "replaceCol" label) "Rat" m n 0
      (fun _ => runReplaceColRatDims m n))
  return lines

def appendPrebuiltElementaryShapeBenchmarks (cfg : Config) (lines : Array String)
    (label : String) {m n : Nat} (A : DenseMatrix m n Rat) : IO (Array String) := do
  let mut lines := lines
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" (elementaryName "swapRow" label) "Rat" m n 0
      (fun _ => runSwapRowRatFrom A))
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" (elementaryName "factor" label) "Rat" m n 0
      (fun _ => runFactorRatFrom A))
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" (elementaryName "replace" label) "Rat" m n 0
      (fun _ => runReplaceRatFrom A))
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" (elementaryName "swapCol" label) "Rat" m n 0
      (fun _ => runSwapColRatFrom A))
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" (elementaryName "factorCol" label) "Rat" m n 0
      (fun _ => runFactorColRatFrom A))
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" (elementaryName "replaceCol" label) "Rat" m n 0
      (fun _ => runReplaceColRatFrom A))
  return lines

def appendRectShapeBenchmarks (cfg : Config) (lines : Array String) (label : String)
    (m n : Nat) : IO (Array String) := do
  let mut lines := lines
  lines := lines.push
    (← measurePure cfg "compiler_dense" s!"of_{label}" "Nat" m n 0
      (fun _ => runOfNatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_dense" s!"ofMatrix_{label}" "Nat" m n 0
      (fun _ => runOfMatrixNatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_dense" s!"toMatrix_{label}" "Nat" m n 0
      (fun _ => runToMatrixNatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_dense" s!"get_{label}" "Nat" m n 0
      (fun _ => runGetCheckedNatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_dense" s!"get!_{label}" "Nat" m n 0
      (fun _ => runGetUncheckedNatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_dense" s!"set_{label}" "Nat" m n 0
      (fun _ => runSetCheckedNatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_dense" s!"set!_{label}" "Nat" m n 0
      (fun _ => runSetUncheckedNatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_dense" s!"add_{label}" "Int" m n 0
      (fun _ => runAddIntDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_dense" s!"smul_{label}" "Int" m n 0
      (fun _ => runSmulIntDims m n))
  if Nat.max m n <= effectiveRatMax cfg then
    lines ← appendElementaryShapeBenchmarks cfg lines label m n
  if Nat.max m n <= effectiveStringMax cfg then
    lines := lines.push
      (← measurePure cfg "compiler_dense" s!"toString_{label}" "Nat" m n 0
        (fun _ => runToStringNatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_dense" s!"transpose_{label}" "Int" m n 0
      (fun _ => runTransposeIntDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_mathlib" s!"construct_{label}" "Nat" m n 0
      (fun _ => runMatrixConstructNatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_mathlib" s!"get_{label}" "Nat" m n 0
      (fun _ => runMatrixGetNatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_mathlib" s!"add_{label}" "Int" m n 0
      (fun _ => runMatrixAddIntDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_mathlib" s!"smul_{label}" "Int" m n 0
      (fun _ => runMatrixSmulIntDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_mathlib" s!"transpose_{label}" "Int" m n 0
      (fun _ => runMatrixTransposeIntDims m n))
  return lines

def appendMulShapeBenchmarks (cfg : Config) (lines : Array String) (label element : String)
    (m k n : Nat) (denseAction matrixAction : Unit → Nat) : IO (Array String) := do
  let mut lines := lines
  lines := lines.push
    (← measurePure cfg "compiler_dense" s!"mul_{label}" element m n k denseAction)
  lines := lines.push
    (← measurePure cfg "compiler_mathlib" s!"mul_{label}" element m n k matrixAction)
  return lines

def appendPrebuiltSquareBenchmarks (cfg : Config) (lines : Array String) (n : Nat) :
    IO (Array String) := do
  let mut lines := lines
  -- Prebuilding inputs here isolates operation runtime from DenseMatrix
  -- construction, which is reported separately by the non-prebuilt cases.
  let denseNatGet := denseNat n n 19
  let denseNatGetUnchecked := denseNat n n 23
  let denseNatSetChecked := denseNat n n 29
  let denseNatSetUnchecked := denseNat n n 37
  let denseIntA := denseInt n n 43
  let denseIntB := denseInt n n 47
  let denseIntSmul := denseInt n n 53
  let denseNatString := denseNat n n 101
  let denseRatA := denseRat n n 79
  let denseRatB := denseRat n n 83
  let denseRatElem := denseRat n n 269
  let denseRatREF := denseRat n n 157
  let denseRatRREF := denseRat n n 163
  let denseRatLU := denseRat n n 167
  let denseRatDet := denseRat n n 173
  let matrixNatGet := matrixNat n n 19
  let matrixIntA := matrixInt n n 43
  let matrixIntB := matrixInt n n 47
  let matrixIntSmul := matrixInt n n 53
  let matrixRatA := matrixRat n n 79
  let matrixRatB := matrixRat n n 83
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" "get" "Nat" n n 0
      (fun _ => checksumDenseChecked natCode denseNatGet))
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" "get!" "Nat" n n 0
      (fun _ => checksumDenseUnchecked natCode denseNatGetUnchecked))
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" "set" "Nat" n n 0
      (fun _ => runSetCheckedNatFrom denseNatSetChecked 31))
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" "set!" "Nat" n n 0
      (fun _ => runSetUncheckedNatFrom denseNatSetUnchecked 41))
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" "add" "Int" n n 0
      (fun _ => checksumDenseUnchecked intCode (DenseMatrix.add denseIntA denseIntB)))
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" "smul" "Int" n n 0
      (fun _ => checksumDenseUnchecked intCode (DenseMatrix.smul (-7 : Int) denseIntSmul)))
  if n <= effectiveStringMax cfg then
    lines := lines.push
      (← measurePure cfg "compiler_dense_prebuilt" "toString" "Nat" n n 0
        (fun _ => (toString denseNatString).length))
  if n ≠ 0 then
    let denseIntTranspose := denseInt n n 59
    let denseNatMulA := denseNat n n 61
    let denseNatMulB := denseNat n n 67
    let denseIntMulA := denseInt n (n + 1) 71
    let denseIntMulB := denseInt (n + 1) (n + 2) 73
    let denseRatMulA := denseRat n n 89
    let denseRatMulB := denseRat n n 97
    lines := lines.push
      (← measurePure cfg "compiler_dense_prebuilt" "transpose" "Int" n n 0
        (fun _ => runTransposeIntFrom denseIntTranspose))
    lines := lines.push
      (← measurePure cfg "compiler_dense_prebuilt" "mul_square" "Nat" n n n
        (fun _ => runMulNatFrom denseNatMulA denseNatMulB))
    lines := lines.push
      (← measurePure cfg "compiler_dense_prebuilt" "mul_rect" "Int" n (n + 2) (n + 1)
        (fun _ => runMulIntFrom denseIntMulA denseIntMulB))
    if n <= effectiveRatMax cfg then
      lines := lines.push
        (← measurePure cfg "compiler_dense_prebuilt" "mul_square" "Rat" n n n
          (fun _ => runMulRatFrom denseRatMulA denseRatMulB))
  if n <= effectiveRatMax cfg then
    lines ← appendPrebuiltElementaryShapeBenchmarks cfg lines "" denseRatElem
    lines := lines.push
      (← measurePure cfg "compiler_dense_prebuilt" "add" "Rat" n n 0
        (fun _ => checksumDenseUnchecked ratCode (DenseMatrix.add denseRatA denseRatB)))
    lines := lines.push
      (← measurePure cfg "compiler_dense_prebuilt" "rowEchelonForm" "Rat" n n 0
        (fun _ => runRowEchelonFormRatFrom denseRatREF))
    lines := lines.push
      (← measurePure cfg "compiler_dense_prebuilt" "reducedRowEchelonForm" "Rat" n n 0
        (fun _ => runReducedRowEchelonFormRatFrom denseRatRREF))
    lines := lines.push
      (← measurePure cfg "compiler_dense_prebuilt" "luFactorization" "Rat" n n 0
        (fun _ => runLUFactorizationRatFrom denseRatLU))
    lines := lines.push
      (← measurePure cfg "compiler_dense_prebuilt" "gaussDet" "Rat" n n 0
        (fun _ => runGaussDetRatFrom denseRatDet))
    lines := lines.push
      (← measurePure cfg "compiler_dense_prebuilt" "luDet" "Rat" n n 0
        (fun _ => runLUDetRatFrom denseRatDet))
  lines := lines.push
    (← measurePure cfg "compiler_mathlib_prebuilt" "get" "Nat" n n 0
      (fun _ => checksumMatrix natCode matrixNatGet))
  lines := lines.push
    (← measurePure cfg "compiler_mathlib_prebuilt" "add" "Int" n n 0
      (fun _ => checksumMatrix intCode (matrixIntA + matrixIntB)))
  lines := lines.push
    (← measurePure cfg "compiler_mathlib_prebuilt" "smul" "Int" n n 0
      (fun _ => checksumMatrix intCode
        (Matrix.of fun i j => (-7 : Int) * matrixIntSmul i j)))
  if n ≠ 0 then
    let matrixIntTranspose := matrixInt n n 59
    let matrixNatMulA := matrixNat n n 61
    let matrixNatMulB := matrixNat n n 67
    let matrixIntMulA := matrixInt n (n + 1) 71
    let matrixIntMulB := matrixInt (n + 1) (n + 2) 73
    let matrixRatMulA := matrixRat n n 89
    let matrixRatMulB := matrixRat n n 97
    lines := lines.push
      (← measurePure cfg "compiler_mathlib_prebuilt" "transpose" "Int" n n 0
        (fun _ => checksumMatrix intCode matrixIntTranspose.transpose))
    lines := lines.push
      (← measurePure cfg "compiler_mathlib_prebuilt" "mul_square" "Nat" n n n
        (fun _ => checksumMatrix natCode (matrixNatMulA * matrixNatMulB)))
    lines := lines.push
      (← measurePure cfg "compiler_mathlib_prebuilt" "mul_rect" "Int" n (n + 2) (n + 1)
        (fun _ => checksumMatrix intCode (matrixIntMulA * matrixIntMulB)))
    if n <= effectiveRatMax cfg then
      lines := lines.push
        (← measurePure cfg "compiler_mathlib_prebuilt" "mul_square" "Rat" n n n
          (fun _ => checksumMatrix ratCode (matrixRatMulA * matrixRatMulB)))
  if n <= effectiveRatMax cfg then
    lines := lines.push
      (← measurePure cfg "compiler_mathlib_prebuilt" "add" "Rat" n n 0
        (fun _ => checksumMatrix ratCode (matrixRatA + matrixRatB)))
  return lines

def appendPrebuiltRectShapeBenchmarks (cfg : Config) (lines : Array String) (label : String)
    (m n : Nat) : IO (Array String) := do
  let mut lines := lines
  let denseNatGet := denseNat m n 181
  let denseNatGetUnchecked := denseNat m n 191
  let denseNatSetChecked := denseNat m n 193
  let denseNatSetUnchecked := denseNat m n 199
  let denseIntA := denseInt m n 223
  let denseIntB := denseInt m n 227
  let denseIntSmul := denseInt m n 229
  let denseRatElem := denseRat m n 269
  let denseNatString := denseNat m n 263
  let matrixNatGet := matrixNat m n 181
  let matrixIntA := matrixInt m n 223
  let matrixIntB := matrixInt m n 227
  let matrixIntSmul := matrixInt m n 229
  let matrixIntTranspose := matrixInt m n 233
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" s!"get_{label}" "Nat" m n 0
      (fun _ => checksumDenseChecked natCode denseNatGet))
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" s!"get!_{label}" "Nat" m n 0
      (fun _ => checksumDenseUnchecked natCode denseNatGetUnchecked))
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" s!"set_{label}" "Nat" m n 0
      (fun _ => runSetCheckedNatFrom denseNatSetChecked 197))
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" s!"set!_{label}" "Nat" m n 0
      (fun _ => runSetUncheckedNatFrom denseNatSetUnchecked 211))
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" s!"add_{label}" "Int" m n 0
      (fun _ => checksumDenseUnchecked intCode (DenseMatrix.add denseIntA denseIntB)))
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" s!"smul_{label}" "Int" m n 0
      (fun _ => checksumDenseUnchecked intCode (DenseMatrix.smul (-7 : Int) denseIntSmul)))
  if Nat.max m n <= effectiveRatMax cfg then
    lines ← appendPrebuiltElementaryShapeBenchmarks cfg lines label denseRatElem
  if Nat.max m n <= effectiveStringMax cfg then
    lines := lines.push
      (← measurePure cfg "compiler_dense_prebuilt" s!"toString_{label}" "Nat" m n 0
        (fun _ => (toString denseNatString).length))
  if m ≠ 0 ∧ n ≠ 0 then
    let denseIntTranspose := denseInt m n 233
    lines := lines.push
      (← measurePure cfg "compiler_dense_prebuilt" s!"transpose_{label}" "Int" m n 0
        (fun _ => runTransposeIntFrom denseIntTranspose))
  lines := lines.push
    (← measurePure cfg "compiler_mathlib_prebuilt" s!"get_{label}" "Nat" m n 0
      (fun _ => checksumMatrix natCode matrixNatGet))
  lines := lines.push
    (← measurePure cfg "compiler_mathlib_prebuilt" s!"add_{label}" "Int" m n 0
      (fun _ => checksumMatrix intCode (matrixIntA + matrixIntB)))
  lines := lines.push
    (← measurePure cfg "compiler_mathlib_prebuilt" s!"smul_{label}" "Int" m n 0
      (fun _ => checksumMatrix intCode
        (Matrix.of fun i j => (-7 : Int) * matrixIntSmul i j)))
  lines := lines.push
    (← measurePure cfg "compiler_mathlib_prebuilt" s!"transpose_{label}" "Int" m n 0
      (fun _ => checksumMatrix intCode matrixIntTranspose.transpose))
  return lines

def appendPrebuiltMulShapeBenchmarks (cfg : Config) (lines : Array String) (label element : String)
    (m k n : Nat) (denseAction matrixAction : Unit → Nat) : IO (Array String) := do
  let mut lines := lines
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" s!"mul_{label}" element m n k denseAction)
  lines := lines.push
    (← measurePure cfg "compiler_mathlib_prebuilt" s!"mul_{label}" element m n k matrixAction)
  return lines

def appendDegenerateShapeBenchmarks (cfg : Config) (lines : Array String) (label : String)
    (m n : Nat) : IO (Array String) := do
  let mut lines := lines
  -- Degenerate shapes are valid for construction, conversion, access, update,
  -- and pointwise arithmetic; operations needing inhabited positive dimensions
  -- are covered by the guarded rectangular appenders instead.
  lines := lines.push
    (← measurePure cfg "compiler_dense" s!"of_{label}" "Nat" m n 0
      (fun _ => runOfNatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_dense" s!"ofMatrix_{label}" "Nat" m n 0
      (fun _ => runOfMatrixNatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_dense" s!"toMatrix_{label}" "Nat" m n 0
      (fun _ => runToMatrixNatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_dense" s!"get_{label}" "Nat" m n 0
      (fun _ => runGetCheckedNatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_dense" s!"get!_{label}" "Nat" m n 0
      (fun _ => runGetUncheckedNatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_dense" s!"set_{label}" "Nat" m n 0
      (fun _ => runSetCheckedNatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_dense" s!"set!_{label}" "Nat" m n 0
      (fun _ => runSetUncheckedNatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_dense" s!"add_{label}" "Int" m n 0
      (fun _ => runAddIntDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_dense" s!"smul_{label}" "Int" m n 0
      (fun _ => runSmulIntDims m n))
  if Nat.max m n <= effectiveStringMax cfg then
    lines := lines.push
      (← measurePure cfg "compiler_dense" s!"toString_{label}" "Nat" m n 0
        (fun _ => runToStringNatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_mathlib" s!"construct_{label}" "Nat" m n 0
      (fun _ => runMatrixConstructNatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_mathlib" s!"get_{label}" "Nat" m n 0
      (fun _ => runMatrixGetNatDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_mathlib" s!"add_{label}" "Int" m n 0
      (fun _ => runMatrixAddIntDims m n))
  lines := lines.push
    (← measurePure cfg "compiler_mathlib" s!"smul_{label}" "Int" m n 0
      (fun _ => runMatrixSmulIntDims m n))
  let denseNatGet := denseNat m n 281
  let denseNatGetUnchecked := denseNat m n 283
  let denseNatSetChecked := denseNat m n 293
  let denseNatSetUnchecked := denseNat m n 307
  let denseIntA := denseInt m n 311
  let denseIntB := denseInt m n 313
  let denseIntSmul := denseInt m n 317
  let denseNatString := denseNat m n 347
  let matrixNatGet := matrixNat m n 281
  let matrixIntA := matrixInt m n 311
  let matrixIntB := matrixInt m n 313
  let matrixIntSmul := matrixInt m n 317
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" s!"get_{label}" "Nat" m n 0
      (fun _ => checksumDenseChecked natCode denseNatGet))
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" s!"get!_{label}" "Nat" m n 0
      (fun _ => checksumDenseUnchecked natCode denseNatGetUnchecked))
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" s!"set_{label}" "Nat" m n 0
      (fun _ => runSetCheckedNatFrom denseNatSetChecked 331))
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" s!"set!_{label}" "Nat" m n 0
      (fun _ => runSetUncheckedNatFrom denseNatSetUnchecked 337))
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" s!"add_{label}" "Int" m n 0
      (fun _ => checksumDenseUnchecked intCode (DenseMatrix.add denseIntA denseIntB)))
  lines := lines.push
    (← measurePure cfg "compiler_dense_prebuilt" s!"smul_{label}" "Int" m n 0
      (fun _ => checksumDenseUnchecked intCode (DenseMatrix.smul (-7 : Int) denseIntSmul)))
  if Nat.max m n <= effectiveStringMax cfg then
    lines := lines.push
      (← measurePure cfg "compiler_dense_prebuilt" s!"toString_{label}" "Nat" m n 0
        (fun _ => (toString denseNatString).length))
  lines := lines.push
    (← measurePure cfg "compiler_mathlib_prebuilt" s!"get_{label}" "Nat" m n 0
      (fun _ => checksumMatrix natCode matrixNatGet))
  lines := lines.push
    (← measurePure cfg "compiler_mathlib_prebuilt" s!"add_{label}" "Int" m n 0
      (fun _ => checksumMatrix intCode (matrixIntA + matrixIntB)))
  lines := lines.push
    (← measurePure cfg "compiler_mathlib_prebuilt" s!"smul_{label}" "Int" m n 0
      (fun _ => checksumMatrix intCode
        (Matrix.of fun i j => (-7 : Int) * matrixIntSmul i j)))
  return lines

def appendDataProfileSquareBenchmarks (cfg : Config) (lines : Array String) (n : Nat) :
    IO (Array String) := do
  let mut lines := lines
  if n = 0 || n > effectiveDataMax cfg then
    return lines
  -- Value-profile coverage is intentionally square-only: it supplements the
  -- shape sweep with algebraically special data while keeping total suite size
  -- predictable.
  lines := lines.push
    (← measurePureProfile cfg "zero" "compiler_dense" "add" "Int" n n 0
      (fun _ => runAddIntZero n))
  lines := lines.push
    (← measurePureProfile cfg "zero" "compiler_mathlib" "add" "Int" n n 0
      (fun _ => runMatrixAddIntZero n))
  lines := lines.push
    (← measurePureProfile cfg "zero" "compiler_dense" "mul_square" "Nat" n n n
      (fun _ => runMulSquareNatZero n))
  lines := lines.push
    (← measurePureProfile cfg "zero" "compiler_mathlib" "mul_square" "Nat" n n n
      (fun _ => runMatrixMulSquareNatZero n))
  lines := lines.push
    (← measurePureProfile cfg "identity" "compiler_dense" "mul_square" "Nat" n n n
      (fun _ => runMulSquareNatIdentity n))
  lines := lines.push
    (← measurePureProfile cfg "identity" "compiler_mathlib" "mul_square" "Nat" n n n
      (fun _ => runMatrixMulSquareNatIdentity n))
  lines := lines.push
    (← measurePureProfile cfg "large_magnitude" "compiler_dense" "mul_square" "Nat" n n n
      (fun _ => runMulSquareNatBig n))
  lines := lines.push
    (← measurePureProfile cfg "large_magnitude" "compiler_mathlib" "mul_square" "Nat" n n n
      (fun _ => runMatrixMulSquareNatBig n))
  lines := lines.push
    (← measurePureProfile cfg "large_magnitude" "compiler_dense" "add" "Int" n n 0
      (fun _ => runAddIntBig n))
  lines := lines.push
    (← measurePureProfile cfg "large_magnitude" "compiler_mathlib" "add" "Int" n n 0
      (fun _ => runMatrixAddIntBig n))
  lines := lines.push
    (← measurePureProfile cfg "large_magnitude" "compiler_dense" "mul_square" "Int" n n n
      (fun _ => runMulSquareIntBig n))
  lines := lines.push
    (← measurePureProfile cfg "large_magnitude" "compiler_mathlib" "mul_square" "Int" n n n
      (fun _ => runMatrixMulSquareIntBig n))
  if n <= effectiveRatMax cfg then
    lines := lines.push
      (← measurePureProfile cfg "large_magnitude" "compiler_dense" "add" "Rat" n n 0
        (fun _ => runAddRatBig n))
    lines := lines.push
      (← measurePureProfile cfg "large_magnitude" "compiler_mathlib" "add" "Rat" n n 0
        (fun _ => runMatrixAddRatBig n))
    lines := lines.push
      (← measurePureProfile cfg "large_magnitude" "compiler_dense" "mul_square" "Rat" n n n
        (fun _ => runMulSquareRatBig n))
    lines := lines.push
      (← measurePureProfile cfg "large_magnitude" "compiler_mathlib" "mul_square" "Rat" n n n
        (fun _ => runMatrixMulSquareRatBig n))
  let denseIntZeroA := denseIntZero n n
  let denseIntZeroB := denseIntZero n n
  let matrixIntZeroA := matrixIntZero n n
  let matrixIntZeroB := matrixIntZero n n
  let denseNatZeroA := denseNatZero n n
  let denseNatZeroB := denseNatZero n n
  let matrixNatZeroA := matrixNatZero n n
  let matrixNatZeroB := matrixNatZero n n
  let denseNatIdentityA := denseNatIdentity n
  let denseNatIdentityB := denseNatIdentity n
  let matrixNatIdentityA := matrixNatIdentity n
  let matrixNatIdentityB := matrixNatIdentity n
  let denseNatBigA := denseNatBig n n 103
  let denseNatBigB := denseNatBig n n 107
  let matrixNatBigA := matrixNatBig n n 103
  let matrixNatBigB := matrixNatBig n n 107
  let denseIntBigA := denseIntBig n n 109
  let denseIntBigB := denseIntBig n n 113
  let matrixIntBigA := matrixIntBig n n 109
  let matrixIntBigB := matrixIntBig n n 113
  let denseIntBigMulA := denseIntBig n n 127
  let denseIntBigMulB := denseIntBig n n 131
  let matrixIntBigMulA := matrixIntBig n n 127
  let matrixIntBigMulB := matrixIntBig n n 131
  lines := lines.push
    (← measurePureProfile cfg "zero" "compiler_dense_prebuilt" "add" "Int" n n 0
      (fun _ => checksumDenseUnchecked intCode (DenseMatrix.add denseIntZeroA denseIntZeroB)))
  lines := lines.push
    (← measurePureProfile cfg "zero" "compiler_mathlib_prebuilt" "add" "Int" n n 0
      (fun _ => checksumMatrix intCode (matrixIntZeroA + matrixIntZeroB)))
  lines := lines.push
    (← measurePureProfile cfg "zero" "compiler_dense_prebuilt" "mul_square" "Nat" n n n
      (fun _ => runMulNatFrom denseNatZeroA denseNatZeroB))
  lines := lines.push
    (← measurePureProfile cfg "zero" "compiler_mathlib_prebuilt" "mul_square" "Nat" n n n
      (fun _ => checksumMatrix natCode (matrixNatZeroA * matrixNatZeroB)))
  lines := lines.push
    (← measurePureProfile cfg "identity" "compiler_dense_prebuilt" "mul_square" "Nat" n n n
      (fun _ => runMulNatFrom denseNatIdentityA denseNatIdentityB))
  lines := lines.push
    (← measurePureProfile cfg "identity" "compiler_mathlib_prebuilt" "mul_square" "Nat" n n n
      (fun _ => checksumMatrix natCode (matrixNatIdentityA * matrixNatIdentityB)))
  lines := lines.push
    (← measurePureProfile cfg "large_magnitude" "compiler_dense_prebuilt" "mul_square" "Nat" n n n
      (fun _ => runMulNatFrom denseNatBigA denseNatBigB))
  lines := lines.push
    (← measurePureProfile cfg "large_magnitude" "compiler_mathlib_prebuilt" "mul_square" "Nat" n n n
      (fun _ => checksumMatrix natCode (matrixNatBigA * matrixNatBigB)))
  lines := lines.push
    (← measurePureProfile cfg "large_magnitude" "compiler_dense_prebuilt" "add" "Int" n n 0
      (fun _ => checksumDenseUnchecked intCode (DenseMatrix.add denseIntBigA denseIntBigB)))
  lines := lines.push
    (← measurePureProfile cfg "large_magnitude" "compiler_mathlib_prebuilt" "add" "Int" n n 0
      (fun _ => checksumMatrix intCode (matrixIntBigA + matrixIntBigB)))
  lines := lines.push
    (← measurePureProfile cfg "large_magnitude" "compiler_dense_prebuilt" "mul_square" "Int" n n n
      (fun _ => runMulIntFrom denseIntBigMulA denseIntBigMulB))
  lines := lines.push
    (← measurePureProfile cfg "large_magnitude" "compiler_mathlib_prebuilt" "mul_square" "Int" n n n
      (fun _ => checksumMatrix intCode (matrixIntBigMulA * matrixIntBigMulB)))
  if n <= effectiveRatMax cfg then
    let denseRatBigA := denseRatBig n n 137
    let denseRatBigB := denseRatBig n n 139
    let matrixRatBigA := matrixRatBig n n 137
    let matrixRatBigB := matrixRatBig n n 139
    let denseRatBigMulA := denseRatBig n n 149
    let denseRatBigMulB := denseRatBig n n 151
    let matrixRatBigMulA := matrixRatBig n n 149
    let matrixRatBigMulB := matrixRatBig n n 151
    lines := lines.push
      (← measurePureProfile cfg "large_magnitude" "compiler_dense_prebuilt" "add" "Rat" n n 0
        (fun _ => checksumDenseUnchecked ratCode (DenseMatrix.add denseRatBigA denseRatBigB)))
    lines := lines.push
      (← measurePureProfile cfg "large_magnitude" "compiler_mathlib_prebuilt" "add" "Rat" n n 0
        (fun _ => checksumMatrix ratCode (matrixRatBigA + matrixRatBigB)))
    lines := lines.push
      (← measurePureProfile cfg "large_magnitude" "compiler_dense_prebuilt" "mul_square" "Rat" n n n
        (fun _ => runMulRatFrom denseRatBigMulA denseRatBigMulB))
    lines := lines.push
      (← measurePureProfile cfg "large_magnitude" "compiler_mathlib_prebuilt" "mul_square"
        "Rat" n n n (fun _ => checksumMatrix ratCode (matrixRatBigMulA * matrixRatBigMulB)))
  return lines

def runBenchmarks (cfg : Config) : IO (Array String) := do
  let mut lines : Array String := #[]
  -- The scheduler emits construction, operation, reference, prebuilt, data
  -- profile, and shape-variation records for each configured base size.  This
  -- order keeps related JSONL records adjacent for human inspection.
  for n in effectiveSizes cfg do
    lines := lines.push (← measurePure cfg "compiler_dense" "of" "Nat" n n 0 (fun _ => runOfNat n))
    lines := lines.push
      (← measurePure cfg "compiler_dense" "ofMatrix" "Nat" n n 0 (fun _ => runOfMatrixNat n))
    lines := lines.push
      (← measurePure cfg "compiler_dense" "toMatrix" "Nat" n n 0 (fun _ => runToMatrixNat n))
    lines := lines.push
      (← measurePure cfg "compiler_dense" "get" "Nat" n n 0 (fun _ => runGetCheckedNat n))
    lines := lines.push
      (← measurePure cfg "compiler_dense" "get!" "Nat" n n 0 (fun _ => runGetUncheckedNat n))
    lines := lines.push
      (← measurePure cfg "compiler_dense" "set" "Nat" n n 0 (fun _ => runSetCheckedNat n))
    lines := lines.push
      (← measurePure cfg "compiler_dense" "set!" "Nat" n n 0 (fun _ => runSetUncheckedNat n))
    lines := lines.push
      (← measurePure cfg "compiler_dense" "add" "Int" n n 0 (fun _ => runAddInt n))
    lines := lines.push
      (← measurePure cfg "compiler_dense" "smul" "Int" n n 0 (fun _ => runSmulInt n))
    if n <= effectiveStringMax cfg then
      lines := lines.push
        (← measurePure cfg "compiler_dense" "toString" "Nat" n n 0
          (fun _ => runToStringNat n))
    if n ≠ 0 then
      lines := lines.push
        (← measurePure cfg "compiler_dense" "transpose" "Int" n n 0
          (fun _ => runTransposeInt n))
      lines := lines.push
        (← measurePure cfg "compiler_dense" "mul_square" "Nat" n n n
          (fun _ => runMulSquareNat n))
      lines := lines.push
        (← measurePure cfg "compiler_dense" "mul_rect" "Int" n (n + 2) (n + 1)
          (fun _ => runMulRectInt n))
    if n <= effectiveRatMax cfg then
      lines := lines.push
        (← measurePure cfg "compiler_dense" "add" "Rat" n n 0 (fun _ => runAddRat n))
      lines ← appendElementaryShapeBenchmarks cfg lines "" n n
      if n ≠ 0 then
        lines := lines.push
          (← measurePure cfg "compiler_dense" "mul_square" "Rat" n n n
            (fun _ => runMulSquareRat n))
    lines := lines.push
      (← measurePure cfg "compiler_mathlib" "construct" "Nat" n n 0
        (fun _ => runMatrixConstructNat n))
    lines := lines.push
      (← measurePure cfg "compiler_mathlib" "get" "Nat" n n 0 (fun _ => runMatrixGetNat n))
    lines := lines.push
      (← measurePure cfg "compiler_mathlib" "add" "Int" n n 0 (fun _ => runMatrixAddInt n))
    lines := lines.push
      (← measurePure cfg "compiler_mathlib" "smul" "Int" n n 0 (fun _ => runMatrixSmulInt n))
    lines := lines.push
      (← measurePure cfg "compiler_mathlib" "transpose" "Int" n n 0
        (fun _ => runMatrixTransposeInt n))
    lines := lines.push
      (← measurePure cfg "compiler_mathlib" "mul_square" "Nat" n n n
        (fun _ => runMatrixMulSquareNat n))
    lines := lines.push
      (← measurePure cfg "compiler_mathlib" "mul_rect" "Int" n (n + 2) (n + 1)
        (fun _ => runMatrixMulRectInt n))
    if n <= effectiveRatMax cfg then
      lines := lines.push
        (← measurePure cfg "compiler_mathlib" "add" "Rat" n n 0
          (fun _ => runMatrixAddRat n))
      lines := lines.push
        (← measurePure cfg "compiler_mathlib" "mul_square" "Rat" n n n
          (fun _ => runMatrixMulSquareRat n))
    lines ← appendPrebuiltSquareBenchmarks cfg lines n
    lines ← appendDataProfileSquareBenchmarks cfg lines n
    if n ≠ 0 then
      let wideCols := n + n
      let tallRows := n + n
      lines ← appendDegenerateShapeBenchmarks cfg lines "zero_rows" 0 n
      lines ← appendDegenerateShapeBenchmarks cfg lines "zero_cols" n 0
      lines ← appendRectShapeBenchmarks cfg lines "wide" n wideCols
      lines ← appendRectShapeBenchmarks cfg lines "tall" tallRows n
      lines ← appendPrebuiltRectShapeBenchmarks cfg lines "wide" n wideCols
      lines ← appendPrebuiltRectShapeBenchmarks cfg lines "tall" tallRows n
      lines ← appendMulShapeBenchmarks cfg lines "wide_inner" "Nat" n wideCols n
        (fun _ => runMulNatDims n wideCols n)
        (fun _ => runMatrixMulNatDims n wideCols n)
      lines ← appendMulShapeBenchmarks cfg lines "tall_output" "Int" tallRows n n
        (fun _ => runMulIntDims tallRows n n)
        (fun _ => runMatrixMulIntDims tallRows n n)
      lines ← appendMulShapeBenchmarks cfg lines "skinny_inner" "Nat" n 4 n
        (fun _ => runMulNatDims n 4 n)
        (fun _ => runMatrixMulNatDims n 4 n)
      let denseWideA := denseNat n wideCols 239
      let denseWideB := denseNat wideCols n 241
      let matrixWideA := matrixNat n wideCols 239
      let matrixWideB := matrixNat wideCols n 241
      let denseTallA := denseInt tallRows n 251
      let denseTallB := denseInt n n 257
      let matrixTallA := matrixInt tallRows n 251
      let matrixTallB := matrixInt n n 257
      let denseSkinnyA := denseNat n 4 239
      let denseSkinnyB := denseNat 4 n 241
      let matrixSkinnyA := matrixNat n 4 239
      let matrixSkinnyB := matrixNat 4 n 241
      lines ← appendPrebuiltMulShapeBenchmarks cfg lines "wide_inner" "Nat" n wideCols n
        (fun _ => runMulNatFrom denseWideA denseWideB)
        (fun _ => checksumMatrix natCode (matrixWideA * matrixWideB))
      lines ← appendPrebuiltMulShapeBenchmarks cfg lines "tall_output" "Int" tallRows n n
        (fun _ => runMulIntFrom denseTallA denseTallB)
        (fun _ => checksumMatrix intCode (matrixTallA * matrixTallB))
      lines ← appendPrebuiltMulShapeBenchmarks cfg lines "skinny_inner" "Nat" n 4 n
        (fun _ => runMulNatFrom denseSkinnyA denseSkinnyB)
        (fun _ => checksumMatrix natCode (matrixSkinnyA * matrixSkinnyB))
  return lines

/-- Write benchmark records either to stdout or to the requested JSONL file. -/
def writeOutput (cfg : Config) (lines : Array String) : IO Unit := do
  let content := String.intercalate "\n" lines.toList ++ "\n"
  match cfg.jsonl with
  | some "-" => IO.print content
  | some path =>
      IO.FS.writeFile path content
      IO.eprintln s!"wrote {lines.size} benchmark records to {path}"
  | none => IO.print content

end DenseMatrixBench
