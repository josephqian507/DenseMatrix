/-
Copyright (c) 2026 Joseph Qian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Qian, Junye Ji, Dhruv Bhatia
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
import ProvableComputation.LinearAlgebra.DenseMatrix.Basic

/-!
# Gaussian Elimination Definitions

This file contains executable row operations used by the Gaussian elimination routines,
together with the structured public result type for row reduction.

## Main definitions

- `DenseMatrix.RowOp` is an inductive type representing the three elementary row operations.
- `DenseMatrix.swapRow` swaps two rows of a `DenseMatrix`.
- `DenseMatrix.scaleRow` scales one row of a `DenseMatrix` by some scalar.
- `DenseMatrix.replaceRow` adds a multiple of one row of a `DenseMatrix` to another row.
- `DenseMatrix.rowReductionResult` contains a `DenseMatrix` and a list of the `RowOps` used to
  obtain it.
-/

open DenseMatrix

universe u v

variable {α : Type u} [Field α] [DecidableEq α]
variable {m n : ℕ}

namespace DenseMatrix

/-! ## Row operations -/

/-- A logged elementary row operation on `m` rows over `α`. -/
inductive RowOp (m : ℕ) (α : Type v) : Type (v + 1) where
  | swap : Fin m → Fin m → RowOp m α
  | scale : Fin m → α → RowOp m α
  | replace : Fin m → Fin m → α → RowOp m α

/-- The condition under which a row-operation certificate represents an invertible operation.

Swaps are always invertible; scaling requires a nonzero scalar; and replacement must use
distinct source and target rows. -/
def RowOp.IsInvertible : RowOp m α → Prop
  | .swap _ _ => True
  | .scale _ c => c ≠ 0
  | .replace src tgt _ => src ≠ tgt

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

/-- Add a multiple of one row to another row. -/
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
      simp only [toMatrix, scaleRow, Matrix.mul_apply, Matrix.transvection, of_apply]
      rw [Fintype.sum_eq_single r]
      · simp
      · intro b hb
        simp [Ne.symm hb]
    · simp only [toMatrix, scaleRow, Matrix.mul_apply, Matrix.transvection, Matrix.of_apply,
        of_apply, ↓reduceIte, Matrix.add_apply, hi]
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
      · simp only [toMatrix, replaceRow, scaleRow, Matrix.mul_apply, Matrix.transvection,
          ↓reduceIte, of_apply, Matrix.of_apply, Matrix.add_apply, hi]
        rw [Fintype.sum_eq_single i]
        · simp [Ne.symm hi]
        · intro b hb
          simp [Ne.symm hb, Ne.symm hi]
    · by_cases hi : i = tgt
      · subst i
        simp only [toMatrix, replaceRow, Matrix.mul_apply, Matrix.transvection, ↓reduceIte,
          of_apply, Matrix.of_apply, Matrix.add_apply, h]
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
      · simp only [toMatrix, replaceRow, Matrix.mul_apply, Matrix.transvection, ↓reduceIte,
          of_apply, Matrix.of_apply, Matrix.add_apply, h, hi]
        rw [Fintype.sum_eq_single i]
        · simp [Matrix.single, Ne.symm hi]
        · intro b hb
          simp [Matrix.single, Ne.symm hb, Ne.symm hi]

theorem toMatrix_scaleRow_eq_rowScale_mul_toMatrix {m n : Nat} {α : Type u} [CommRing α]
    (A : DenseMatrix m n α) (r : Fin m) (c : α) : toMatrix (scaleRow A r c)
    = Matrix.rowScale r c * toMatrix A := by
  rw [Matrix.rowScale_mul]
  ext i j
  rw [Matrix.updateRow_apply]
  simp only [Pi.smul_apply, smul_eq_mul, get_toMatrix]
  change (scaleRow A r c).get i j = if i = r then c * A.toMatrix r j else A.get i j
  rw [get_toMatrix, scaleRow, of_apply]
  split <;> simp_all

/-- Apply one row operation certificate to a dense matrix. -/
def applyRowOp {m n : Nat} {α : Type u} [Semiring α]
    (A : DenseMatrix m n α) (op : RowOp m α) : DenseMatrix m n α :=
  match op with
  | .swap i j => swapRow A i j
  | .scale i c => scaleRow A i c
  | .replace src tgt k => replaceRow A src tgt k

/-- A valid row-operation certificate preserves row equivalence in the Mathlib matrix view. -/
theorem RowOp.rowEquivalent_toMatrix {m n : Nat} {α : Type u} [Field α]
    (op : RowOp m α) (h : op.IsInvertible) (A : DenseMatrix m n α) :
    Matrix.RowEquivalent A.toMatrix (applyRowOp A op).toMatrix := by
  cases op with
  | swap i j =>
      simpa [applyRowOp, toMatrix_swap_eq_swap_toMatrix] using
        Matrix.rowEquivalent_swap A.toMatrix i j
  | scale i c =>
      rw [applyRowOp, toMatrix_scaleRow_eq_rowScale_mul_toMatrix, ← Units.val_mk0 h]
      exact Matrix.rowEquivalent_rowScale A.toMatrix i (Units.mk0 c h)
  | replace src tgt c =>
      simpa [applyRowOp, toMatrix_replace_eq_replace_toMatrix] using
        Matrix.rowEquivalent_transvection A.toMatrix tgt src h.symm c

/-- Elementary matrix corresponding to one row operation certificate. -/
def elementaryMatrixOfRowOp {m : Nat} {α : Type u} [Semiring α] [NeZero m]
    (op : RowOp m α) : DenseMatrix m m α :=
  applyRowOp 1 op

@[simp]
theorem get_swapRow {m n : Nat} {α : Type u}
    (A : DenseMatrix m n α) (r₁ r₂ : Fin m) (i : Fin m) (j : Fin n) :
    (swapRow A r₁ r₂).get i j =
      if i = r₁ then A.get r₂ j else if i = r₂ then A.get r₁ j else A.get i j := by
  simp [swapRow]

@[simp]
theorem get_scaleRow {m n : Nat} {α : Type u} [Mul α]
    (A : DenseMatrix m n α) (r : Fin m) (c : α) (i : Fin m) (j : Fin n) :
    (scaleRow A r c).get i j = if i = r then c * A.get i j else A.get i j := by
  simp [scaleRow]

@[simp]
theorem get_replaceRow {m n : Nat} {α : Type u} [Semiring α]
    (A : DenseMatrix m n α) (src tgt : Fin m) (k : α) (i : Fin m) (j : Fin n) :
    (replaceRow A src tgt k).get i j =
      if i = tgt then A.get tgt j + k * A.get src j else A.get i j := by
  by_cases hst : src = tgt
  · subst tgt
    by_cases hi : i = src
    · subst i
      simp [replaceRow, add_mul, add_comm]
    · simp [replaceRow, hi]
  · simp [replaceRow, hst]

theorem swap_inv {m n : Nat} {α : Type u}
    (A : DenseMatrix m n α) (r₁ r₂ : Fin m) :
    swapRow (swapRow A r₁ r₂) r₁ r₂ = A := by
  apply_fun toMatrix using DenseMatrix.equivMatrix.injective
  ext i j
  simp only [get_toMatrix, get_swapRow]
  split_ifs with h1 h2 h3
  · rw [h2, ← h1]
  · rw [← h1]
  · rw [← h3]
  · rfl

theorem scaleRow_inv {m n : Nat} {α : Type u} [Field α]
    (A : DenseMatrix m n α) (r : Fin m) (s : α) (hs : s ≠ 0) :
    scaleRow (scaleRow A r s) r s⁻¹ = A := by
  apply_fun toMatrix using DenseMatrix.equivMatrix.injective
  ext i j
  simp only [get_toMatrix, get_scaleRow]
  by_cases hi : i = r
  · simp [hi, hs]
  · simp [hi]

theorem replace_inv {m n : Nat} {α : Type u} [Ring α]
    (A : DenseMatrix m n α) (src tgt : Fin m) (k : α) (h : src ≠ tgt) :
    replaceRow (replaceRow A src tgt k) src tgt (-k) = A := by
  apply_fun toMatrix using DenseMatrix.equivMatrix.injective
  ext i j
  simp only [get_toMatrix, get_replaceRow]
  by_cases hi : i = tgt
  · simp [hi, h]
  · simp [hi]

theorem elementaryMatrixOfRowOp_mul_eq_applyRowOp
    {m n : Nat} {α : Type u} [CommRing α] [Inhabited α] [NeZero m] [NeZero n]
    (op : RowOp m α) (A : DenseMatrix m n α) :
    elementaryMatrixOfRowOp op * A = applyRowOp A op := by
  apply_fun toMatrix using DenseMatrix.equivMatrix.injective
  rw [mul_toMatrix]
  cases op <;>
    simp [elementaryMatrixOfRowOp, applyRowOp, toMatrix_swap_eq_swap_toMatrix,
      toMatrix_scale_eq_scale_toMatrix, toMatrix_replace_eq_replace_toMatrix, one_toMatrix]

/-- The structure containing the result of a row reduction routine. -/
structure RowReductionResult (m n : Nat) (α : Type u) where
  matrix : DenseMatrix m n α
  steps : List (RowOp m α)

end DenseMatrix
