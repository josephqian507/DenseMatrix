/-
Copyright (c) 2026 Provable Computation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Provable Computation contributors
-/

import ProvableComputation.LinearAlgebra.DenseMatrix.GaussianElimination.Defs
import ProvableComputation.LinearAlgebra.DenseMatrix.Echelon.Basic

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

/-! ## Direct left multiplication -/

/-- Left multiplication of a dense matrix by a function-backed square matrix. -/
def leftMul {m n : Nat} {R : Type u} [Semiring R]
    (U : Matrix (Fin m) (Fin m) R) (A : DenseMatrix m n R) : DenseMatrix m n R :=
  DenseMatrix.of fun i j ↦ ∑ k, U i k * A.get k j

@[simp]
theorem get_leftMul {m n : Nat} {R : Type u} [Semiring R]
    (U : Matrix (Fin m) (Fin m) R) (A : DenseMatrix m n R) (i : Fin m) (j : Fin n) :
    (leftMul U A).get i j = ∑ k, U i k * A.get k j := by
  simp [leftMul]

@[simp]
theorem toMatrix_leftMul {m n : Nat} {R : Type u} [Semiring R]
    (U : Matrix (Fin m) (Fin m) R) (A : DenseMatrix m n R) :
    toMatrix (leftMul U A) = U * toMatrix A := by
  ext i j
  change (leftMul U A).get i j = ∑ k, U i k * A.get k j
  exact get_leftMul U A i j

@[simp]
theorem leftMul_one {m n : Nat} {R : Type u} [Semiring R] (A : DenseMatrix m n R) :
    leftMul (1 : Matrix (Fin m) (Fin m) R) A = A := by
  apply toMatrix_injective
  simp

theorem leftMul_mul {m n : Nat} {R : Type u} [Semiring R]
    (U V : Matrix (Fin m) (Fin m) R) (A : DenseMatrix m n R) :
    leftMul (U * V) A = leftMul U (leftMul V A) := by
  apply toMatrix_injective
  simp [Matrix.mul_assoc]

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

/-! ## Row equivalence -/

/-- Row-equivalence via direct left multiplication by a unit square matrix. -/
def RowEquivalent {m n : Nat} {R : Type u} [Field R]
    (A B : DenseMatrix m n R) : Prop :=
  ∃ U : (Matrix (Fin m) (Fin m) R)ˣ, B = leftMul (U : Matrix (Fin m) (Fin m) R) A

theorem RowEquivalent.refl {m n : Nat} {R : Type u} [Field R]
    (A : DenseMatrix m n R) : RowEquivalent A A := by
  refine ⟨1, ?_⟩
  simp

theorem RowEquivalent.symm {m n : Nat} {R : Type u} [Field R]
    {A B : DenseMatrix m n R} (h : RowEquivalent A B) : RowEquivalent B A := by
  rcases h with ⟨U, rfl⟩
  refine ⟨U⁻¹, ?_⟩
  rw [← leftMul_mul]
  simp

theorem RowEquivalent.trans {m n : Nat} {R : Type u} [Field R]
    {A B C : DenseMatrix m n R} (hAB : RowEquivalent A B) (hBC : RowEquivalent B C) :
    RowEquivalent A C := by
  rcases hAB with ⟨U, rfl⟩
  rcases hBC with ⟨V, rfl⟩
  refine ⟨V * U, ?_⟩
  exact (leftMul_mul (V : Matrix (Fin m) (Fin m) R) U A).symm

instance rowEquivalentSetoid {m n : Nat} {R : Type u} [Field R] :
    Setoid (DenseMatrix m n R) where
  r := RowEquivalent
  iseqv := ⟨RowEquivalent.refl, RowEquivalent.symm, RowEquivalent.trans⟩

/-- `B` is an echelon-form representative of `A`. -/
def IsEchelonFormOf {m n : Nat} {R : Type u} [Field R]
    (A B : DenseMatrix m n R) : Prop :=
  RowEquivalent A B ∧ IsEchelonForm B

/-- Extract row equivalence from a dense echelon-form representative. -/
theorem IsEchelonFormOf.rowEquivalent {m n : Nat} {R : Type u} [Field R]
    {A B : DenseMatrix m n R} (h : IsEchelonFormOf A B) : RowEquivalent A B :=
  h.1

/-- Extract echelon form from a dense echelon-form representative. -/
theorem IsEchelonFormOf.echelon {m n : Nat} {R : Type u} [Field R]
    {A B : DenseMatrix m n R} (h : IsEchelonFormOf A B) : IsEchelonForm B :=
  h.2

/-- Build a dense echelon-form representative from its two defining properties. -/
theorem isEchelonFormOf_mk {m n : Nat} {R : Type u} [Field R]
    {A B : DenseMatrix m n R} (hRow : RowEquivalent A B) (hEch : IsEchelonForm B) :
    IsEchelonFormOf A B :=
  ⟨hRow, hEch⟩

end DenseMatrix
