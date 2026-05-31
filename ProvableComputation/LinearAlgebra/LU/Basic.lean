/-
Copyright (c) 2026 Provable Computation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Provable Computation contributors
-/

import ProvableComputation.LinearAlgebra.LU.Defs
import ProvableComputation.LinearAlgebra.GaussianElimination.Elementary
import ProvableComputation.LinearAlgebra.GaussianElimination.Rref

/-!
# LU Basic Algorithm

This module turns the row-operation log produced by Gaussian elimination into permutation
and lower-triangular factors, and exposes the structured public LU-factorization API.
-/

variable {R : Type} [Field R] [DecidableEq R]
variable {a : Nat} {b : Nat}

namespace LUFactorizationInternal

def permutationOfSwaps (swaps : List (Fin a × Fin a)) : squareMatrix a R :=
  swaps.foldl (fun acc ij => ColumnElementary.swapCol acc ij.1 ij.2) 1

def lowerOfSwaps
    (swaps : List (Fin a × Fin a)) (MInv : squareMatrix a R) : squareMatrix a R :=
  swaps.foldl (fun acc ij => swapRow acc ij.1 ij.2) MInv

def buildPLStep
    (state : List (Fin a × Fin a) × squareMatrix a R)
    (op : RowOp a R) : List (Fin a × Fin a) × squareMatrix a R :=
  let swaps := state.1
  let MInv := state.2
  match op with
  | .swap i j => (swaps.concat (i, j), ColumnElementary.swapCol MInv i j)
  | .factor row scale => (swaps, ColumnElementary.factorCol MInv row scale⁻¹)
  | .replace use toReplace scale =>
      if use = toReplace then
        (swaps, ColumnElementary.factorCol MInv toReplace (scale + 1)⁻¹)
      else
        (swaps, ColumnElementary.replaceCol MInv use toReplace (-scale))

/-- Replay a row-operation log into the permutation and lower-triangular bookkeeping factors. -/
def buildPLFromSteps (steps : List (RowOp a R)) : squareMatrix a R × squareMatrix a R :=
  let (swaps, MInv) :=
    steps.foldl (LUFactorizationInternal.buildPLStep (R := R)) ([], 1)
  let P := LUFactorizationInternal.permutationOfSwaps (R := R) swaps
  let L := LUFactorizationInternal.lowerOfSwaps (R := R) swaps MInv
  (P, L)

/-- Internal LU factorization together with the row-operation log that produced `U`. -/
structure RawFactorizationWithSteps (a b : Nat) (R : Type) where
  P : squareMatrix a R
  L : squareMatrix a R
  U : Matrix (Fin a) (Fin b) R
  steps : List (RowOp a R)

/-- Internal LU factorization with the REF row-operation log retained. -/
def rawFactorizationWithSteps (M : Matrix (Fin a) (Fin b) R) :
    LUFactorizationInternal.RawFactorizationWithSteps a b R :=
  let (U, steps) := GaussianEliminationInternal.rawRowEchelonForm M
  let (P, L) := buildPLFromSteps steps
  { P := P, L := L, U := U, steps := steps }

/-- Internal tuple-valued LU factorization used by the proof files. -/
def rawFactorization (M : Matrix (Fin a) (Fin b) R) :
    squareMatrix a R × (squareMatrix a R × Matrix (Fin a) (Fin b) R) :=
  let (U, steps) := GaussianEliminationInternal.rawRowEchelonForm M
  let (P, L) := buildPLFromSteps steps
  (P, (L, U))

end LUFactorizationInternal

namespace DenseMatrix

/-
Dense LU bookkeeping replays the same row-operation log as the Matrix version,
but it builds `P` and `L` in row-major storage.  Swaps are accumulated as column
operations on the permutation side and row operations on the lower-factor side,
matching the existing `buildPLFromSteps` contract.
-/
def permutationOfSwaps (swaps : List (Fin a × Fin a)) : DenseMatrix a a R :=
  swaps.foldl (fun acc ij => DenseMatrix.swapCol acc ij.1 ij.2) DenseMatrix.identity

def lowerOfSwaps
    (swaps : List (Fin a × Fin a)) (MInv : DenseMatrix a a R) : DenseMatrix a a R :=
  swaps.foldl (fun acc ij => DenseMatrix.swapRow acc ij.1 ij.2) MInv

def buildPLStep
    (state : List (Fin a × Fin a) × DenseMatrix a a R)
    (op : RowOp a R) : List (Fin a × Fin a) × DenseMatrix a a R :=
  let swaps := state.1
  let MInv := state.2
  match op with
  | .swap i j => (swaps.concat (i, j), DenseMatrix.swapCol MInv i j)
  | .factor row scale => (swaps, DenseMatrix.factorCol MInv row scale⁻¹)
  | .replace use toReplace scale =>
      if use = toReplace then
        (swaps, DenseMatrix.factorCol MInv toReplace (scale + 1)⁻¹)
      else
        (swaps, DenseMatrix.replaceCol MInv use toReplace (-scale))

/-- Dense replay of a row-operation log into the permutation and lower factors. -/
def buildPLFromSteps (steps : List (RowOp a R)) : DenseMatrix a a R × DenseMatrix a a R :=
  let (swaps, MInv) := steps.foldl (DenseMatrix.buildPLStep (R := R)) ([], DenseMatrix.identity)
  let P := DenseMatrix.permutationOfSwaps (R := R) swaps
  let L := DenseMatrix.lowerOfSwaps (R := R) swaps MInv
  (P, L)

/-
The fold bridge is deliberately proved at the accumulator level.  LU correctness
needs the final dense `P` and `L` to match the Matrix replay exactly, and an
accumulator lemma prevents later changes to the fold seed from weakening that
connection.
-/
omit [Field R] [DecidableEq R] in
private theorem foldlSwapCol_toMatrix
    (swaps : List (Fin a × Fin a)) (acc : DenseMatrix a a R) :
    (swaps.foldl (fun acc ij => DenseMatrix.swapCol acc ij.1 ij.2) acc).toMatrix =
      swaps.foldl (fun acc ij => ColumnElementary.swapCol acc ij.1 ij.2) acc.toMatrix := by
  induction swaps generalizing acc with
  | nil => rfl
  | cons ij swaps ih =>
      simpa [List.foldl, ColumnElementary.swapCol] using
        ih (acc := DenseMatrix.swapCol acc ij.1 ij.2)

omit [DecidableEq R] in
@[simp]
theorem permutationOfSwaps_toMatrix (swaps : List (Fin a × Fin a)) :
    (DenseMatrix.permutationOfSwaps (R := R) swaps).toMatrix =
      LUFactorizationInternal.permutationOfSwaps (R := R) swaps := by
  simp [DenseMatrix.permutationOfSwaps, LUFactorizationInternal.permutationOfSwaps,
    foldlSwapCol_toMatrix]

omit [Field R] [DecidableEq R] in
private theorem foldlSwapRow_toMatrix
    (swaps : List (Fin a × Fin a)) (acc : DenseMatrix a a R) :
    (swaps.foldl (fun acc ij => DenseMatrix.swapRow acc ij.1 ij.2) acc).toMatrix =
      swaps.foldl (fun acc ij => _root_.swapRow acc ij.1 ij.2) acc.toMatrix := by
  induction swaps generalizing acc with
  | nil => rfl
  | cons ij swaps ih =>
      simpa [List.foldl] using
        ih (acc := DenseMatrix.swapRow acc ij.1 ij.2)

omit [Field R] [DecidableEq R] in
@[simp]
theorem lowerOfSwaps_toMatrix
    (swaps : List (Fin a × Fin a)) (MInv : DenseMatrix a a R) :
    (DenseMatrix.lowerOfSwaps (R := R) swaps MInv).toMatrix =
      LUFactorizationInternal.lowerOfSwaps (R := R) swaps MInv.toMatrix := by
  simp [DenseMatrix.lowerOfSwaps, LUFactorizationInternal.lowerOfSwaps, foldlSwapRow_toMatrix]

private theorem buildPLStep_toMatrix
    (state : List (Fin a × Fin a) × DenseMatrix a a R) (op : RowOp a R) :
    let dense := DenseMatrix.buildPLStep (R := R) state op
    let matrix := LUFactorizationInternal.buildPLStep (R := R) (state.1, state.2.toMatrix) op
    (dense.1, dense.2.toMatrix) = matrix := by
  cases state with
  | mk swaps MInv =>
      cases op with
      | swap i j =>
          simp [DenseMatrix.buildPLStep, LUFactorizationInternal.buildPLStep,
            ColumnElementary.swapCol]
      | factor row scale =>
          simp [DenseMatrix.buildPLStep, LUFactorizationInternal.buildPLStep,
            ColumnElementary.factorCol]
      | replace use toReplace scale =>
          by_cases h : use = toReplace
          · simp [DenseMatrix.buildPLStep, LUFactorizationInternal.buildPLStep,
              ColumnElementary.factorCol, h]
          · simp [DenseMatrix.buildPLStep, LUFactorizationInternal.buildPLStep,
              ColumnElementary.replaceCol, h]

private theorem foldlBuildPLStep_toMatrix
    (steps : List (RowOp a R)) (state : List (Fin a × Fin a) × DenseMatrix a a R) :
    let dense := steps.foldl (DenseMatrix.buildPLStep (R := R)) state
    let matrix :=
      steps.foldl (LUFactorizationInternal.buildPLStep (R := R)) (state.1, state.2.toMatrix)
    (dense.1, dense.2.toMatrix) = matrix := by
  induction steps generalizing state with
  | nil => rfl
  | cons op steps ih =>
      rw [List.foldl, List.foldl]
      rcases hdense : DenseMatrix.buildPLStep (R := R) state op with ⟨swaps, MInv⟩
      have hstep := buildPLStep_toMatrix (R := R) (state := state) (op := op)
      have hmatrix :
          LUFactorizationInternal.buildPLStep (R := R) (state.1, state.2.toMatrix) op =
            (swaps, MInv.toMatrix) := by
        simpa [hdense] using hstep.symm
      rw [hmatrix]
      simpa using ih (state := (swaps, MInv))

@[simp]
theorem buildPLFromSteps_toMatrix (steps : List (RowOp a R)) :
    ((DenseMatrix.buildPLFromSteps (R := R) steps).1.toMatrix,
        (DenseMatrix.buildPLFromSteps (R := R) steps).2.toMatrix) =
      LUFactorizationInternal.buildPLFromSteps (R := R) steps := by
  rw [DenseMatrix.buildPLFromSteps, LUFactorizationInternal.buildPLFromSteps]
  rcases hdense :
      steps.foldl (DenseMatrix.buildPLStep (R := R)) ([], DenseMatrix.identity) with
    ⟨swaps, MInv⟩
  have hfold := foldlBuildPLStep_toMatrix (R := R) (steps := steps)
    (state := (([] : List (Fin a × Fin a)), (DenseMatrix.identity : DenseMatrix a a R)))
  rw [hdense] at hfold
  simp only [DenseMatrix.toMatrix_identity] at hfold
  rw [← hfold]
  simp

/-- Structured DenseMatrix output of LU factorization. -/
structure LUFactors (a b : Nat) (R : Type) where
  P : DenseMatrix a a R
  L : DenseMatrix a a R
  U : DenseMatrix a b R

/-- DenseMatrix LU factorization together with the row-operation log that produced `U`. -/
structure LUFactorsWithSteps (a b : Nat) (R : Type) where
  P : DenseMatrix a a R
  L : DenseMatrix a a R
  U : DenseMatrix a b R
  steps : List (RowOp a R)

/-- DenseMatrix-facing LU factorization with the REF row-operation log retained. -/
def luFactorizationWithSteps (M : DenseMatrix a b R) :
    DenseMatrix.LUFactorsWithSteps a b R :=
  let raw := DenseMatrix.rawRowEchelonForm M
  let PL := DenseMatrix.buildPLFromSteps raw.2
  { P := PL.1, L := PL.2, U := raw.1, steps := raw.2 }

/-- DenseMatrix-facing LU factorization, backed by the dense-native echelon pipeline. -/
def luFactorization (M : DenseMatrix a b R) : DenseMatrix.LUFactors a b R :=
  let raw := DenseMatrix.rawRowEchelonForm M
  let PL := DenseMatrix.buildPLFromSteps raw.2
  { P := PL.1, L := PL.2, U := raw.1 }

/-
`luFactorization_toMatrix` is the handoff point from executable DenseMatrix code
back to the proof-oriented Matrix factorization.  It combines the row-echelon
bridge with the PL replay bridge, giving later reconstruction and determinant
theorems the exact factors they already know how to reason about.
-/
@[simp]
theorem luFactorization_toMatrix (M : DenseMatrix a b R) :
    let lu := DenseMatrix.luFactorization (R := R) M
    (lu.P.toMatrix, lu.L.toMatrix, lu.U.toMatrix) =
      let raw := LUFactorizationInternal.rawFactorization (R := R) M.toMatrix
      (raw.1, raw.2.1, raw.2.2) := by
  rw [luFactorization]
  rcases hdense : DenseMatrix.rawRowEchelonForm M with ⟨U, steps⟩
  have hraw := DenseMatrix.rawRowEchelonForm_toMatrix (given := M)
  rw [hdense] at hraw
  have hU :
      U.toMatrix = (GaussianEliminationInternal.rawRowEchelonForm M.toMatrix).1 :=
    congrArg Prod.fst hraw
  have hsteps :
      steps = (GaussianEliminationInternal.rawRowEchelonForm M.toMatrix).2 :=
    congrArg Prod.snd hraw
  have hPL := DenseMatrix.buildPLFromSteps_toMatrix (R := R)
    (steps := (GaussianEliminationInternal.rawRowEchelonForm M.toMatrix).2)
  have hP :
      (DenseMatrix.buildPLFromSteps (R := R)
          (GaussianEliminationInternal.rawRowEchelonForm M.toMatrix).2).1.toMatrix =
        (LUFactorizationInternal.buildPLFromSteps (R := R)
          (GaussianEliminationInternal.rawRowEchelonForm M.toMatrix).2).1 := by
    simpa using congrArg Prod.fst hPL
  have hL :
      (DenseMatrix.buildPLFromSteps (R := R)
          (GaussianEliminationInternal.rawRowEchelonForm M.toMatrix).2).2.toMatrix =
        (LUFactorizationInternal.buildPLFromSteps (R := R)
          (GaussianEliminationInternal.rawRowEchelonForm M.toMatrix).2).2 := by
    simpa using congrArg Prod.snd hPL
  change
      ((DenseMatrix.buildPLFromSteps (R := R) steps).1.toMatrix,
        (DenseMatrix.buildPLFromSteps (R := R) steps).2.toMatrix,
        U.toMatrix) =
        let raw := LUFactorizationInternal.rawFactorization (R := R) M.toMatrix
        (raw.1, raw.2.1, raw.2.2)
  rw [hsteps, hU]
  change
      ((DenseMatrix.buildPLFromSteps (R := R)
          (GaussianEliminationInternal.rawRowEchelonForm M.toMatrix).2).1.toMatrix,
        (DenseMatrix.buildPLFromSteps (R := R)
          (GaussianEliminationInternal.rawRowEchelonForm M.toMatrix).2).2.toMatrix,
        (GaussianEliminationInternal.rawRowEchelonForm M.toMatrix).1) =
        ((LUFactorizationInternal.buildPLFromSteps (R := R)
          (GaussianEliminationInternal.rawRowEchelonForm M.toMatrix).2).1,
        (LUFactorizationInternal.buildPLFromSteps (R := R)
          (GaussianEliminationInternal.rawRowEchelonForm M.toMatrix).2).2,
        (GaussianEliminationInternal.rawRowEchelonForm M.toMatrix).1)
  rw [hP, hL]

@[simp]
theorem luFactorizationWithSteps_toMatrix (M : DenseMatrix a b R) :
    let lu := DenseMatrix.luFactorizationWithSteps (R := R) M
    (lu.P.toMatrix, lu.L.toMatrix, lu.U.toMatrix, lu.steps) =
      let raw := LUFactorizationInternal.rawFactorizationWithSteps (R := R) M.toMatrix
      (raw.P, raw.L, raw.U, raw.steps) := by
  rw [luFactorizationWithSteps, LUFactorizationInternal.rawFactorizationWithSteps]
  rcases hdense : DenseMatrix.rawRowEchelonForm M with ⟨U, steps⟩
  have hraw := DenseMatrix.rawRowEchelonForm_toMatrix (given := M)
  rw [hdense] at hraw
  have hU :
      U.toMatrix = (GaussianEliminationInternal.rawRowEchelonForm M.toMatrix).1 :=
    congrArg Prod.fst hraw
  have hsteps :
      steps = (GaussianEliminationInternal.rawRowEchelonForm M.toMatrix).2 :=
    congrArg Prod.snd hraw
  have hPL := DenseMatrix.buildPLFromSteps_toMatrix (R := R)
    (steps := (GaussianEliminationInternal.rawRowEchelonForm M.toMatrix).2)
  have hP :
      (DenseMatrix.buildPLFromSteps (R := R)
          (GaussianEliminationInternal.rawRowEchelonForm M.toMatrix).2).1.toMatrix =
        (LUFactorizationInternal.buildPLFromSteps (R := R)
          (GaussianEliminationInternal.rawRowEchelonForm M.toMatrix).2).1 := by
    simpa using congrArg Prod.fst hPL
  have hL :
      (DenseMatrix.buildPLFromSteps (R := R)
          (GaussianEliminationInternal.rawRowEchelonForm M.toMatrix).2).2.toMatrix =
        (LUFactorizationInternal.buildPLFromSteps (R := R)
          (GaussianEliminationInternal.rawRowEchelonForm M.toMatrix).2).2 := by
    simpa using congrArg Prod.snd hPL
  simp [hU, hsteps, hP, hL]

@[simp]
theorem luFactorization_P_toMatrix (M : DenseMatrix a b R) :
    (DenseMatrix.luFactorization (R := R) M).P.toMatrix =
      (LUFactorizationInternal.rawFactorization (R := R) M.toMatrix).1 := by
  have h := luFactorization_toMatrix (R := R) (M := M)
  exact congrArg Prod.fst h

@[simp]
theorem luFactorization_L_toMatrix (M : DenseMatrix a b R) :
    (DenseMatrix.luFactorization (R := R) M).L.toMatrix =
      (LUFactorizationInternal.rawFactorization (R := R) M.toMatrix).2.1 := by
  have h := luFactorization_toMatrix (R := R) (M := M)
  exact congrArg (fun x => x.2.1) h

@[simp]
theorem luFactorization_U_toMatrix (M : DenseMatrix a b R) :
    (DenseMatrix.luFactorization (R := R) M).U.toMatrix =
      (LUFactorizationInternal.rawFactorization (R := R) M.toMatrix).2.2 := by
  have h := luFactorization_toMatrix (R := R) (M := M)
  exact congrArg (fun x => x.2.2) h

end DenseMatrix

namespace Matrix

/-
The public Matrix factorization keeps the established structured return type,
but the work is performed by the dense backend.  The surrounding bridge theorems
ensure this routing change is computational only, not a change in the
mathematical API.
-/
/-- Structured public LU factorization routed through the DenseMatrix executable surface. -/
def luFactorization (M : Matrix (Fin a) (Fin b) R) : LUFactors a b R :=
  let dense := DenseMatrix.luFactorization (DenseMatrix.ofMatrix M)
  { P := dense.P.toMatrix, L := dense.L.toMatrix, U := dense.U.toMatrix }

end Matrix
