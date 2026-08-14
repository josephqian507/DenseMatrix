/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
import ProvableComputation.LinearAlgebra.DenseMatrix.Defs

/-!
# Dense Matrix Echelon Predicates

This module defines row-zero, pivot, echelon, and reduced-echelon predicates directly
for `DenseMatrix`.
-/

namespace DenseMatrix

universe u

variable {R : Type u} [Field R]

/-- A dense matrix row is zero when every entry in the row is zero. -/
def RowIsZero {m n : Nat} (A : DenseMatrix m n R) (i : Fin m) : Prop :=
  ∀ j, A.get i j = 0

/--
Column `p` is the pivot of row `i` when its entry is nonzero and every earlier entry in
the row is zero.
-/
def IsPivot {m n : Nat} (A : DenseMatrix m n R) (i : Fin m) (p : Fin n) : Prop :=
  A.get i p ≠ 0 ∧ ∀ j < p, A.get i j = 0

/-- A row cannot have two distinct pivot columns. -/
theorem IsPivot.eq_of_left {m n : Nat} {A : DenseMatrix m n R}
    {i : Fin m} {p q : Fin n} (hp : IsPivot A i p) (hq : IsPivot A i q) : p = q := by
  have hnot_lt_pq : ¬ p < q := fun hlt ↦ hp.left (hq.right p hlt)
  have hnot_lt_qp : ¬ q < p := fun hlt ↦ hq.left (hp.right q hlt)
  exact le_antisymm (le_of_not_gt hnot_lt_qp) (le_of_not_gt hnot_lt_pq)

/-- A zero row cannot contain a pivot. -/
theorem RowIsZero.not_isPivot {m n : Nat} {A : DenseMatrix m n R}
    {i : Fin m} {p : Fin n} (hzero : RowIsZero A i) (hp : IsPivot A i p) : False :=
  hp.left (hzero p)

/-- Dense row-echelon form. -/
structure IsEchelonForm {m n : Nat} (A : DenseMatrix m n R) : Prop where
  /-- Every row is zero or has a pivot. -/
  row_zero_or_pivot :
    ∀ i, RowIsZero A i ∨ ∃ p : Fin n, IsPivot A i p
  /-- Zero rows are followed only by zero rows. -/
  zero_rows_bottom :
    ∀ i j, i < j → RowIsZero A i → RowIsZero A j
  /-- Pivots of later rows occur in strictly later columns. -/
  pivots_strictly_increasing :
    ∀ i j p q, i < j → IsPivot A i p → IsPivot A j q → p < q

/-- Entries below a pivot of a dense echelon matrix are zero. -/
theorem IsEchelonForm.pivot_column_zero_below
    {m n : Nat} {A : DenseMatrix m n R} (h : IsEchelonForm A) :
    ∀ i r p, i < r → IsPivot A i p → A.get r p = 0 := by
  intro i r p hir hp
  rcases h.row_zero_or_pivot r with hzero | ⟨q, hq⟩
  · exact hzero p
  · exact hq.2 p (h.pivots_strictly_increasing i r p q hir hp hq)

/-- Dense reduced row-echelon form. -/
structure IsReducedEchelonForm {m n : Nat} (A : DenseMatrix m n R) : Prop where
  /-- The matrix is in row-echelon form. -/
  echelon : IsEchelonForm A
  /-- Every pivot is one. -/
  pivot_is_one :
    ∀ i p, IsPivot A i p → A.get i p = 1
  /-- Entries above a pivot are zero. -/
  pivot_column_zero_above :
    ∀ i r p, r < i → IsPivot A i p → A.get r p = 0

end DenseMatrix
