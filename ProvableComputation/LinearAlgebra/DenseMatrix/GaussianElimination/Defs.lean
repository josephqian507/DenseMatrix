import Mathlib.Data.Matrix.Basic
import ProvableComputation.LinearAlgebra.DenseMatrix.Defs

/-!
# Gaussian Elimination Definitions

This module contains the executable row-operation primitives and pivot search used by the
Gaussian elimination routines, together with the structured public result type for row
reduction.
-/

open DenseMatrix

universe u v

variable {α : Type u} [Field α] [DecidableEq α]
variable {m n : ℕ}

namespace DenseMatrix

/-- A logged elementary row operation on `m` rows over `α`. -/
inductive RowOp (m : ℕ) (α : Type v) : Type (v + 1) where
  | swap : Fin m → Fin m → RowOp m α
  | factor : Fin m → α → RowOp m α
  | replace : Fin m → Fin m → α → RowOp m α

/-- Swap two rows of a dense matrix. -/
def swapRow {m n : Nat} {α : Type u}
    (A : DenseMatrix m n α) (r1 r2 : Fin m) : DenseMatrix m n α :=
  of fun i j =>
    if i = r1 then
      A.get r2 j
    else if i = r2 then
      A.get r1 j
    else
      A.get i j

/-- Scale one row of a dense matrix by a scalar. -/
def scaleRow {m n : Nat} {α : Type u} [Mul α]
    (A : DenseMatrix m n α) (r : Fin m) (c : α) : DenseMatrix m n α :=
  of fun i j =>
    if i = r then
      c * A.get i j
    else
      A.get i j

/-- Replace `tgt` by `tgt + k * src`, with the diagonal case treated as scaling. -/
def replaceRow {m n : Nat} {α : Type u} [Add α] [Mul α] [One α]
    (A : DenseMatrix m n α) (src tgt : Fin m) (k : α) : DenseMatrix m n α :=
  if src = tgt then
    scaleRow A tgt (k + 1)
  else
    of fun i j =>
      if i = tgt then
        A.get tgt j + k * A.get src j
      else
        A.get i j

private theorem get_of {m n : Nat} {α : Type u} (f : Fin m → Fin n → α)
    (i : Fin m) (j : Fin n) : get (of f) i j = f i j := by
  exact of_apply f i j

theorem toMatrix_swap_eq_swap_toMatrix {m n : Nat} {α : Type u} [Semiring α]
    (A : DenseMatrix m n α) (r1 r2 : Fin m) : toMatrix (swapRow A r1 r2)
    = (Matrix.swap α r1 r2) * (toMatrix A) := by
    ext i j
    by_cases hi1 : i = r1
    · subst i
      simp [toMatrix, swapRow]
    · by_cases hi2 : i = r2
      · subst i
        simp [toMatrix, swapRow, hi1]
      · rw [Matrix.swap_mul_of_ne hi1 hi2]
        simp [toMatrix, swapRow, hi1, hi2]

theorem toMatrix_scale_eq_scale_toMatrix {m n : Nat} {α : Type u} [CommRing α]
    (A : DenseMatrix m n α) (r : Fin m) (c : α) : toMatrix (scaleRow A r c)
    = (Matrix.transvection r r (c - 1)) * (toMatrix A) := by
    ext i j
    by_cases hi : i = r
    · subst i
      simp only [toMatrix, scaleRow, Matrix.mul_apply, Matrix.transvection, get_of]
      rw [Fintype.sum_eq_single r]
      · simp
      · intro b hb
        simp [Ne.symm hb]
    · simp [toMatrix, scaleRow, Matrix.mul_apply, Matrix.transvection, get_of, hi]
      rw [Fintype.sum_eq_single i]
      · simp [Ne.symm hi]
      · intro b hb
        simp [Ne.symm hb, Ne.symm hi]

theorem toMatrix_replace_eq_replace_toMatrix {m n : Nat} {α : Type u} [CommRing α]
    (A : DenseMatrix m n α) (src tgt : Fin m) (k : α) :
    toMatrix (replaceRow A src tgt k) = (Matrix.transvection tgt src k) * (toMatrix A) :=
  by
    ext i j
    by_cases h : src = tgt
    · subst src
      by_cases hi : i = tgt
      · subst i
        simp only [toMatrix, replaceRow, scaleRow, Matrix.mul_apply, Matrix.transvection]
        rw [Fintype.sum_eq_single tgt]
        · simp
          ring
        · intro b hb
          simp [Ne.symm hb]
      · simp [toMatrix, replaceRow, scaleRow, Matrix.mul_apply, Matrix.transvection, get_of, hi]
        rw [Fintype.sum_eq_single i]
        · simp [Ne.symm hi]
        · intro b hb
          simp [Ne.symm hb, Ne.symm hi]
    · by_cases hi : i = tgt
      · subst i
        simp [toMatrix, replaceRow, Matrix.mul_apply, Matrix.transvection, get_of, h]
        rw [show
            (∑ x, ((1 : Matrix (Fin m) (Fin m) α) tgt x +
                Matrix.single tgt src k tgt x) * A.get x j) =
              (∑ x, (1 : Matrix (Fin m) (Fin m) α) tgt x * A.get x j) +
                ∑ x, Matrix.single tgt src k tgt x * A.get x j by
          rw [← Finset.sum_add_distrib]
          congr
          ext x
          ring]
        rw [Fintype.sum_eq_single tgt]
        · rw [Fintype.sum_eq_single src]
          · simp [Matrix.single]
          · intro b hb
            simp [Matrix.single, Ne.symm hb]
        · intro b hb
          simp [Ne.symm hb]
      · simp [toMatrix, replaceRow, Matrix.mul_apply, Matrix.transvection, get_of, h, hi]
        rw [Fintype.sum_eq_single i]
        · simp [Matrix.single, Ne.symm hi]
        · intro b hb
          simp [Matrix.single, Ne.symm hb, Ne.symm hi]

theorem toMatrix_left_mul_eq_zero_iff {m n : Nat} {α : Type u} [Semiring α]
    (U : Matrix (Fin m) (Fin m) α) [Invertible U]
    (A : DenseMatrix m n α)
    (x : Matrix (Fin n) (Fin 1) α) :
    (U * toMatrix A) * x = 0 ↔ toMatrix A * x = 0 := by
  constructor
  · intro h
    have h' : U * (toMatrix A * x) = 0 := by
      simpa [Matrix.mul_assoc] using h
    have hmul := congrArg (fun Y : Matrix (Fin m) (Fin 1) α => ⅟U * Y) h'
    simpa [Matrix.invOf_mul_cancel_left] using hmul
  · intro h
    rw [Matrix.mul_assoc, h, Matrix.mul_zero]

/--
Find the first nonzero pivot entry at or below `startRow` and at or to the right of
`startCol`.
-/
def checkPivot
    (M : DenseMatrix m n α)
    (startRow startCol : Nat) :
    Option (Fin m × Fin n) :=
  let rec scanCol (col : Nat) : Option (Fin m × Fin n) :=
    if hcol : col < n then
      let rec scanRow (row : Nat) : Option (Fin m × Fin n) :=
        if hrow : row < m then
          if M.get ⟨row, hrow⟩ ⟨col, hcol⟩ ≠ 0 then
            some (⟨row, hrow⟩, ⟨col, hcol⟩)
          else
            scanRow (row + 1)
        else
          none
      match scanRow startRow with
      | some p => some p
      | none => scanCol (col + 1)
    else
      none
  scanCol startCol

/-- The public structured result of a row-reduction routine. -/
structure RowReductionResult (m n : Nat) (α : Type) where
  matrix : DenseMatrix m n α
  steps : List (RowOp m α)

end DenseMatrix
