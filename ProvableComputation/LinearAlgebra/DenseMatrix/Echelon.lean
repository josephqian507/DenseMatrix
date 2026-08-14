/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
import ProvableComputation.LinearAlgebra.DenseMatrix.Echelon.Basic
import ProvableComputation.LinearAlgebra.Echelon

/-!
# Dense Matrix Echelon Predicates

This compatibility module relates the native dense echelon predicates to the corresponding
function-backed `Matrix` predicates.
-/

namespace DenseMatrix

universe u

variable {R : Type u} [Field R]

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
    IsEchelonForm A ↔ Matrix.IsEchelonForm (toMatrix A) := by
  constructor
  · intro h
    exact {
      row_zero_or_pivot := h.row_zero_or_pivot
      zero_rows_bottom := h.zero_rows_bottom
      pivots_strictly_increasing := h.pivots_strictly_increasing
    }
  · intro h
    exact {
      row_zero_or_pivot := h.row_zero_or_pivot
      zero_rows_bottom := h.zero_rows_bottom
      pivots_strictly_increasing := h.pivots_strictly_increasing
    }

theorem IsEchelonForm.toMatrix {m n : Nat} {A : DenseMatrix m n R}
    (h : IsEchelonForm A) : Matrix.IsEchelonForm (DenseMatrix.toMatrix A) :=
  (isEchelonForm_iff_toMatrix A).mp h

theorem IsEchelonForm.of_toMatrix {m n : Nat} {A : DenseMatrix m n R}
    (h : Matrix.IsEchelonForm (DenseMatrix.toMatrix A)) : IsEchelonForm A :=
  (isEchelonForm_iff_toMatrix A).mpr h

@[simp]
theorem isReducedEchelonForm_iff_toMatrix {m n : Nat} (A : DenseMatrix m n R) :
    IsReducedEchelonForm A ↔ Matrix.IsReducedEchelonForm (toMatrix A) := by
  constructor
  · intro h
    exact {
      echelon := h.echelon.toMatrix
      pivot_is_one := h.pivot_is_one
      pivot_column_zero_above := h.pivot_column_zero_above
    }
  · intro h
    exact {
      echelon := DenseMatrix.IsEchelonForm.of_toMatrix h.echelon
      pivot_is_one := h.pivot_is_one
      pivot_column_zero_above := h.pivot_column_zero_above
    }

theorem IsReducedEchelonForm.toMatrix {m n : Nat} {A : DenseMatrix m n R}
    (h : IsReducedEchelonForm A) :
    Matrix.IsReducedEchelonForm (DenseMatrix.toMatrix A) :=
  (isReducedEchelonForm_iff_toMatrix A).mp h

theorem IsReducedEchelonForm.of_toMatrix {m n : Nat} {A : DenseMatrix m n R}
    (h : Matrix.IsReducedEchelonForm (DenseMatrix.toMatrix A)) : IsReducedEchelonForm A :=
  (isReducedEchelonForm_iff_toMatrix A).mpr h

end DenseMatrix
