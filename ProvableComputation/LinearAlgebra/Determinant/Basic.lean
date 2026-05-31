/-
Copyright (c) 2026 Provable Computation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Provable Computation contributors
-/

import Mathlib.Algebra.Field.Rat

import ProvableComputation.LinearAlgebra.GaussianElimination.Rref
import ProvableComputation.LinearAlgebra.LU.Defs
import ProvableComputation.LinearAlgebra.LU.Basic

/-!
# Determinant Algorithms

This module contains the executable determinant routines built from Gaussian elimination
and LU factorization, together with namespaced public wrappers on the structured API.
-/

variable {R : Type} [Field R] [DecidableEq R]
variable {n : Nat}
variable {hn : n > 0}

open Matrix

namespace DeterminantInternal

/-
The executable determinant path is driven by a row-operation log.  These
helpers assign the determinant multiplier for each logged operation and then
multiply the whole trace, matching the correctness proof in
`Determinant.Correctness`.
-/
def rowOpDetMultiplier : RowOp n R → R
  | .swap i j => if i = j then 1 else -1
  | .factor _ c => c
  | .replace use toReplace k => if use = toReplace then k + 1 else 1

def detMultiplierOfSteps (steps : List (RowOp n R)) : R :=
  (steps.map rowOpDetMultiplier).prod

def swapRowState (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) (d : R) :
  Matrix (Fin n) (Fin n) R × R :=
  if _h : i = j then
    (M, d)
  else
    (swapRow M i j, -d)

def scaleRowState (M : Matrix (Fin n) (Fin n) R) (i : Fin n) (c : R) (d : R) :
  Matrix (Fin n) (Fin n) R × R :=
  (factor M i c⁻¹, d * c)

/-- Product of the diagonal entries of a square matrix. -/
def diagonalProduct (M : squareMatrix n R) : R :=
  ∏ i : (Fin n), M i i

/-
Legacy Gaussian-elimination determinant loop retained for direct experimentation.
The public determinant implementation below uses the logged row-echelon pipeline
instead, because that path shares proofs and runtime behavior with LU/RREF.
-/
def gaussDetLoop (M : Matrix (Fin n) (Fin n) R) (row : Nat) (d : R) : R :=
  if hrow : row < n then
    match checkPivot M row row with
      | none => 0
      | some (pivotRow, pivotCol) =>
          let rowFin : Fin n := ⟨row, hrow⟩
          let (M, d) := swapRowState M rowFin pivotRow d
          -- let pivotVal := M1 rowFin pivotCol
          -- let (M2, d2) := scaleRowState M1 rowFin pivotVal d1
          let (M, _) :=
            GaussianEliminationInternal.eliminateColCore M rowFin pivotCol List.nil false
          gaussDetLoop M (row + 1) d
  else
    d * diagonalProduct M

/--
Gaussian-elimination determinant computation from the row-echelon operation log.
Row replacement steps contribute multiplier `1`, swaps contribute their sign,
and the diagonal product is taken from the resulting echelon matrix.
-/
def rawGaussDet (M : Matrix (Fin n) (Fin n) R) : R :=
  let (U, steps) := GaussianEliminationInternal.rawRowEchelonForm M
  detMultiplierOfSteps steps * diagonalProduct U

/--
LU determinant computation through the factorization replay. The permutation
sign is read from the same step log that builds `P`; `L` is included in the
runtime path and later proved to contribute diagonal product `1`.
-/
def rawLuDet (M : Matrix (Fin n) (Fin n) R) : R :=
  let lu := LUFactorizationInternal.rawFactorizationWithSteps (R := R) M
  detMultiplierOfSteps lu.steps * diagonalProduct lu.L * diagonalProduct lu.U

end DeterminantInternal

namespace DenseMatrix

/-
Dense determinant routines keep the diagonal product and row-echelon log in
row-major storage until the final bridge theorem.  This avoids converting back
to `Matrix` inside the executable path while preserving `Matrix.det` as the
specification.
-/
/-- Diagonal product of a square dense matrix. -/
def diagonalProduct (M : DenseMatrix n n R) : R :=
  ∏ i : Fin n, M.get i i

omit [DecidableEq R] in
@[simp]
theorem diagonalProduct_toMatrix (M : DenseMatrix n n R) :
    DenseMatrix.diagonalProduct M =
      DeterminantInternal.diagonalProduct M.toMatrix := by
  simp [DenseMatrix.diagonalProduct, DeterminantInternal.diagonalProduct]

/-- DenseMatrix-facing determinant through the LU factorization replay. -/
def luDet (M : DenseMatrix n n R) : R :=
  let lu := DenseMatrix.luFactorizationWithSteps (R := R) M
  DeterminantInternal.detMultiplierOfSteps lu.steps *
    DenseMatrix.diagonalProduct lu.L * DenseMatrix.diagonalProduct lu.U

@[simp]
theorem luDet_toMatrix (M : DenseMatrix n n R) :
    DenseMatrix.luDet M = DeterminantInternal.rawLuDet M.toMatrix := by
  rcases hlu : DenseMatrix.luFactorizationWithSteps (R := R) M with ⟨_, L, U, steps⟩
  have hraw := DenseMatrix.luFactorizationWithSteps_toMatrix (R := R) (M := M)
  rw [hlu] at hraw
  have hL :
      L.toMatrix =
        (LUFactorizationInternal.rawFactorizationWithSteps (R := R) M.toMatrix).L := by
    exact congrArg (fun x => x.2.1) hraw
  have hU :
      U.toMatrix =
        (LUFactorizationInternal.rawFactorizationWithSteps (R := R) M.toMatrix).U := by
    exact congrArg (fun x => x.2.2.1) hraw
  have hsteps :
      steps =
        (LUFactorizationInternal.rawFactorizationWithSteps (R := R) M.toMatrix).steps := by
    exact congrArg (fun x => x.2.2.2) hraw
  simp [DenseMatrix.luDet, DeterminantInternal.rawLuDet, hlu, hL, hU, hsteps]

/-- DenseMatrix-facing Gaussian-elimination determinant. -/
def gaussDet (M : DenseMatrix n n R) : R :=
  let raw := DenseMatrix.rawRowEchelonForm M
  DeterminantInternal.detMultiplierOfSteps raw.2 * DenseMatrix.diagonalProduct raw.1

@[simp]
theorem gaussDet_toMatrix (M : DenseMatrix n n R) :
    DenseMatrix.gaussDet M = DeterminantInternal.rawGaussDet M.toMatrix := by
  rcases hdense : DenseMatrix.rawRowEchelonForm M with ⟨U, steps⟩
  have hraw := DenseMatrix.rawRowEchelonForm_toMatrix (given := M)
  rw [hdense] at hraw
  have hU :
      U.toMatrix = (GaussianEliminationInternal.rawRowEchelonForm M.toMatrix).1 :=
    congrArg Prod.fst hraw
  have hsteps :
      steps = (GaussianEliminationInternal.rawRowEchelonForm M.toMatrix).2 :=
    congrArg Prod.snd hraw
  simp [DenseMatrix.gaussDet, DeterminantInternal.rawGaussDet, hdense, hU, hsteps]

end DenseMatrix

namespace Matrix

/-
The Matrix namespace remains the public user-facing determinant surface.  Calls
are routed through `DenseMatrix.ofMatrix`, so ordinary Matrix users benefit from
the dense runtime backend without changing theorem names or signatures.
-/
/-- Public diagonal product helper for square matrices. -/
def diagonalProduct (M : Matrix (Fin n) (Fin n) R) : R :=
  DeterminantInternal.diagonalProduct M

/-- Structured public determinant computation via Gaussian elimination. -/
def gaussDet (M : Matrix (Fin n) (Fin n) R) : R :=
  DenseMatrix.gaussDet (DenseMatrix.ofMatrix M)

/-- Structured public determinant computation via LU factorization. -/
def luDet (M : Matrix (Fin n) (Fin n) R) : R :=
  DenseMatrix.luDet (DenseMatrix.ofMatrix M)

end Matrix
