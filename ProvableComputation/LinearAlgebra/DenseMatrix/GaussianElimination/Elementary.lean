/-
Copyright (c) 2026 Provable Computation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Provable Computation contributors
-/

import ProvableComputation.LinearAlgebra.DenseMatrix.GaussianElimination.Defs

/-!
# Dense matrix elementary operations

This module provides identity and logged row operations.
-/

universe u

namespace DenseMatrix

variable {m n : Nat}

/-! ## Identity and row operations -/

private theorem toMatrix_injective {m n : Nat} {α : Type u} :
    Function.Injective (@DenseMatrix.toMatrix m n α) := by
  intro A B h
  calc
    A = ofMatrix (toMatrix A) := (ofMatrix_toMatrix A).symm
    _ = ofMatrix (toMatrix B) := congrArg ofMatrix h
    _ = B := ofMatrix_toMatrix B

/-- The dense identity matrix. -/
def identity {n : Nat} {α : Type u} [Zero α] [One α] [DecidableEq (Fin n)] :
    DenseMatrix n n α :=
  of fun i j => if i = j then 1 else 0

@[simp]
theorem get_identity {n : Nat} {α : Type u} [Zero α] [One α] [DecidableEq (Fin n)]
    (i j : Fin n) :
    (identity : DenseMatrix n n α).get i j = if i = j then 1 else 0 := by
  simp [identity]

@[simp]
theorem toMatrix_identity {n : Nat} {α : Type u} [Zero α] [One α] [DecidableEq (Fin n)] :
    toMatrix (identity : DenseMatrix n n α) = (1 : Matrix (Fin n) (Fin n) α) := by
  ext i j
  simp [identity, get_toMatrix, Matrix.one_apply]

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

/-- Apply one shared row-operation certificate to a dense matrix. -/
def applyRowOp {m n : Nat} {α : Type u} [Semiring α]
    (A : DenseMatrix m n α) (op : RowOp m α) : DenseMatrix m n α :=
  match op with
  | .swap i j => swapRow A i j
  | .factor i c => scaleRow A i c
  | .replace src tgt k => replaceRow A src tgt k

/-- Elementary matrix corresponding to one shared row-operation certificate. -/
def elementaryMatrixOfRowOp {m : Nat} {α : Type u} [Semiring α] [NeZero m]
    (op : RowOp m α) : DenseMatrix m m α :=
  applyRowOp identity op

theorem elementaryMatrixOfRowOp_mul_eq_applyRowOp
    {m n : Nat} {α : Type u} [CommRing α] [Inhabited α] [NeZero m] [NeZero n]
    (op : RowOp m α) (A : DenseMatrix m n α) :
    elementaryMatrixOfRowOp op * A = applyRowOp A op := by
  apply toMatrix_injective
  change toMatrix (mul (elementaryMatrixOfRowOp op) A) = toMatrix (applyRowOp A op)
  rw [mul_toMatrix]
  cases op <;>
    simp [elementaryMatrixOfRowOp, applyRowOp, toMatrix_swap_eq_swap_toMatrix,
      toMatrix_scale_eq_scale_toMatrix, toMatrix_replace_eq_replace_toMatrix]

theorem swap_inv {m n : Nat} {α : Type u}
    (A : DenseMatrix m n α) (r₁ r₂ : Fin m) :
    swapRow (swapRow A r₁ r₂) r₁ r₂ = A := by
  apply toMatrix_injective
  ext i j
  simp only [get_toMatrix, get_swapRow]
  split_ifs with h1 h2 h3
  · rw [h2, ← h1]
  · rw [← h1]
  · rw [← h3]
  · rfl

theorem factor_inv {m n : Nat} {α : Type u} [Field α]
    (A : DenseMatrix m n α) (r : Fin m) (s : α) (hs : s ≠ 0) :
    scaleRow (scaleRow A r s) r s⁻¹ = A := by
  apply toMatrix_injective
  ext i j
  simp only [get_toMatrix, get_scaleRow]
  by_cases hi : i = r
  · simp [hi, hs]
  · simp [hi]

theorem replace_inv {m n : Nat} {α : Type u} [Ring α]
    (A : DenseMatrix m n α) (src tgt : Fin m) (k : α) (h : src ≠ tgt) :
    replaceRow (replaceRow A src tgt k) src tgt (-k) = A := by
  apply toMatrix_injective
  ext i j
  simp only [get_toMatrix, get_replaceRow]
  by_cases hi : i = tgt
  · simp [hi, h]
  · simp [hi]

end DenseMatrix
