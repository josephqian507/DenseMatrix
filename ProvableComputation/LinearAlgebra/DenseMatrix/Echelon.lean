/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
import ProvableComputation.LinearAlgebra.DenseMatrix.Defs
import ProvableComputation.LinearAlgebra.Echelon

/-!
# Dense Matrix Echelon Predicates

This module exposes row-zero, pivot, echelon, and reduced-echelon predicates for
`DenseMatrix`. The row and pivot predicates are stated directly using checked dense
matrix access. Echelon structures reuse the corresponding `Matrix` predicates through
`toMatrix`, while constructor and projection theorems preserve a structure-style
DenseMatrix API for downstream proofs.
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

/-- Dense row-echelon form, transported through the function-backed matrix view. -/
def IsEchelonForm {m n : Nat} (A : DenseMatrix m n R) : Prop :=
  Matrix.IsEchelonForm (toMatrix A)

/-- Dense reduced row-echelon form, transported through the function-backed matrix view. -/
def IsReducedEchelonForm {m n : Nat} (A : DenseMatrix m n R) : Prop :=
  Matrix.IsReducedEchelonForm (toMatrix A)

/-! ## Matrix bridge -/

/-- A dense zero row is definitionally the zero row of the function-backed matrix view. -/
@[simp]
theorem rowIsZero_iff_toMatrix {m n : Nat} (A : DenseMatrix m n R) (i : Fin m) :
    RowIsZero A i ↔ Matrix.RowIsZero (DenseMatrix.toMatrix A) i :=
  Iff.rfl

/-- Transport a dense zero-row witness to the function-backed matrix view. -/
theorem RowIsZero.toMatrix {m n : Nat} {A : DenseMatrix m n R} {i : Fin m}
    (h : RowIsZero A i) : Matrix.RowIsZero (DenseMatrix.toMatrix A) i :=
  (rowIsZero_iff_toMatrix A i).mp h

/-- Transport a zero-row witness from the function-backed matrix view. -/
theorem RowIsZero.of_toMatrix {m n : Nat} {A : DenseMatrix m n R} {i : Fin m}
    (h : Matrix.RowIsZero (DenseMatrix.toMatrix A) i) : RowIsZero A i :=
  (rowIsZero_iff_toMatrix A i).mpr h

/-- A dense pivot is definitionally the pivot of the function-backed matrix view. -/
@[simp]
theorem isPivot_iff_toMatrix {m n : Nat}
    (A : DenseMatrix m n R) (i : Fin m) (p : Fin n) :
    IsPivot A i p ↔ Matrix.IsPivot (DenseMatrix.toMatrix A) i p :=
  Iff.rfl

/-- Transport a dense pivot witness to the function-backed matrix view. -/
theorem IsPivot.toMatrix {m n : Nat}
    {A : DenseMatrix m n R} {i : Fin m} {p : Fin n}
    (h : IsPivot A i p) : Matrix.IsPivot (DenseMatrix.toMatrix A) i p :=
  (isPivot_iff_toMatrix A i p).mp h

/-- Transport a pivot witness from the function-backed matrix view. -/
theorem IsPivot.of_toMatrix {m n : Nat}
    {A : DenseMatrix m n R} {i : Fin m} {p : Fin n}
    (h : Matrix.IsPivot (DenseMatrix.toMatrix A) i p) : IsPivot A i p :=
  (isPivot_iff_toMatrix A i p).mpr h

@[simp]
theorem isEchelonForm_iff_toMatrix {m n : Nat} (A : DenseMatrix m n R) :
    IsEchelonForm A ↔ Matrix.IsEchelonForm (toMatrix A) :=
  Iff.rfl

theorem IsEchelonForm.toMatrix {m n : Nat} {A : DenseMatrix m n R}
    (h : IsEchelonForm A) : Matrix.IsEchelonForm (DenseMatrix.toMatrix A) :=
  (isEchelonForm_iff_toMatrix A).mp h

theorem IsEchelonForm.of_toMatrix {m n : Nat} {A : DenseMatrix m n R}
    (h : Matrix.IsEchelonForm (DenseMatrix.toMatrix A)) : IsEchelonForm A :=
  (isEchelonForm_iff_toMatrix A).mpr h

@[simp]
theorem isReducedEchelonForm_iff_toMatrix {m n : Nat} (A : DenseMatrix m n R) :
    IsReducedEchelonForm A ↔ Matrix.IsReducedEchelonForm (toMatrix A) :=
  Iff.rfl

theorem IsReducedEchelonForm.toMatrix {m n : Nat} {A : DenseMatrix m n R}
    (h : IsReducedEchelonForm A) :
    Matrix.IsReducedEchelonForm (DenseMatrix.toMatrix A) :=
  (isReducedEchelonForm_iff_toMatrix A).mp h

theorem IsReducedEchelonForm.of_toMatrix {m n : Nat} {A : DenseMatrix m n R}
    (h : Matrix.IsReducedEchelonForm (DenseMatrix.toMatrix A)) : IsReducedEchelonForm A :=
  (isReducedEchelonForm_iff_toMatrix A).mpr h

/-! ## Structure-style DenseMatrix API -/

/-- Build a dense echelon-form witness from the same fields as `Matrix.IsEchelonForm`. -/
theorem IsEchelonForm.mk {m n : Nat} {A : DenseMatrix m n R}
    (row_zero_or_pivot : ∀ i, RowIsZero A i ∨ ∃ p : Fin n, IsPivot A i p)
    (zero_rows_bottom : ∀ i j, i < j → RowIsZero A i → RowIsZero A j)
    (pivots_strictly_increasing :
      ∀ i j p q, i < j → IsPivot A i p → IsPivot A j q → p < q) :
    IsEchelonForm A :=
  Matrix.IsEchelonForm.mk row_zero_or_pivot zero_rows_bottom pivots_strictly_increasing

/-- Every row of a dense echelon matrix is zero or has a pivot. -/
theorem IsEchelonForm.row_zero_or_pivot {m n : Nat} {A : DenseMatrix m n R}
    (h : IsEchelonForm A) :
    ∀ i, RowIsZero A i ∨ ∃ p : Fin n, IsPivot A i p :=
  h.toMatrix.row_zero_or_pivot

/-- Zero rows of a dense echelon matrix are followed only by zero rows. -/
theorem IsEchelonForm.zero_rows_bottom {m n : Nat} {A : DenseMatrix m n R}
    (h : IsEchelonForm A) :
    ∀ i j, i < j → RowIsZero A i → RowIsZero A j :=
  h.toMatrix.zero_rows_bottom

/-- Pivots of later rows in a dense echelon matrix occur in strictly later columns. -/
theorem IsEchelonForm.pivots_strictly_increasing
    {m n : Nat} {A : DenseMatrix m n R} (h : IsEchelonForm A) :
    ∀ i j p q, i < j → IsPivot A i p → IsPivot A j q → p < q :=
  h.toMatrix.pivots_strictly_increasing

/-- Entries below a pivot of a dense echelon matrix are zero. -/
theorem IsEchelonForm.pivot_column_zero_below
    {m n : Nat} {A : DenseMatrix m n R} (h : IsEchelonForm A) :
    ∀ i r p, i < r → IsPivot A i p → A.get r p = 0 :=
  h.toMatrix.pivot_column_zero_below

/--
Build a dense reduced-echelon-form witness from the same fields as
`Matrix.IsReducedEchelonForm`.
-/
theorem IsReducedEchelonForm.mk {m n : Nat} {A : DenseMatrix m n R}
    (echelon : IsEchelonForm A)
    (pivot_is_one : ∀ i p, IsPivot A i p → A.get i p = 1)
    (pivot_column_zero_above :
      ∀ i r p, r < i → IsPivot A i p → A.get r p = 0) :
    IsReducedEchelonForm A :=
  Matrix.IsReducedEchelonForm.mk echelon.toMatrix pivot_is_one pivot_column_zero_above

/-- A dense reduced-echelon matrix is in echelon form. -/
theorem IsReducedEchelonForm.echelon {m n : Nat} {A : DenseMatrix m n R}
    (h : IsReducedEchelonForm A) : IsEchelonForm A :=
  h.toMatrix.echelon

/-- Every pivot of a dense reduced-echelon matrix is one. -/
theorem IsReducedEchelonForm.pivot_is_one {m n : Nat} {A : DenseMatrix m n R}
    (h : IsReducedEchelonForm A) :
    ∀ i p, IsPivot A i p → A.get i p = 1 :=
  h.toMatrix.pivot_is_one

/-- Entries above a pivot of a dense reduced-echelon matrix are zero. -/
theorem IsReducedEchelonForm.pivot_column_zero_above
    {m n : Nat} {A : DenseMatrix m n R} (h : IsReducedEchelonForm A) :
    ∀ i r p, r < i → IsPivot A i p → A.get r p = 0 :=
  h.toMatrix.pivot_column_zero_above

end DenseMatrix
