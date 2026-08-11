import ProvableComputation.LinearAlgebra.DenseMatrix.Echelon

/-!
# Dense matrix echelon tests

These examples exercise the native DenseMatrix predicates, their Matrix bridges,
and the structure-style echelon and reduced-echelon APIs.
-/

namespace DenseMatrix

private def testZeroRow : DenseMatrix 1 2 Rat :=
  ofMatrix ![![0, 0]]

private def testEchelon : DenseMatrix 2 2 Rat :=
  ofMatrix ![![1, 2], ![0, 3]]

private def testReducedEchelon : DenseMatrix 2 2 Rat :=
  ofMatrix ![![1, 0], ![0, 1]]

private theorem get_ofMatrix_fn {m n : Nat} {α : Type*}
    (M : Fin m → Fin n → α) (i : Fin m) (j : Fin n) :
    get (ofMatrix M) i j = M i j := by
  exact get_ofMatrix M i j

example {R : Type*} [Field R] {m n : Nat} (A : DenseMatrix m n R) (i : Fin m) :
    RowIsZero A i ↔ ∀ j, A.get i j = 0 :=
  Iff.rfl

example {R : Type*} [Field R] {m n : Nat}
    (A : DenseMatrix m n R) (i : Fin m) (p : Fin n) :
    IsPivot A i p ↔ A.get i p ≠ 0 ∧ ∀ j < p, A.get i j = 0 :=
  Iff.rfl

example : RowIsZero testZeroRow 0 := by
  simp [RowIsZero, testZeroRow, get_ofMatrix_fn]

example : IsPivot testEchelon 0 0 := by
  simp [IsPivot, testEchelon, get_ofMatrix_fn]

example : ¬ IsPivot testEchelon 0 1 := by
  simp [IsPivot, testEchelon, get_ofMatrix_fn]

section MatrixBridge

variable {R : Type*} [Field R] {m n : Nat}
variable {A : DenseMatrix m n R} {i : Fin m} {p : Fin n}

example (h : RowIsZero A i) : Matrix.RowIsZero (DenseMatrix.toMatrix A) i :=
  h.toMatrix

example (h : Matrix.RowIsZero (DenseMatrix.toMatrix A) i) : RowIsZero A i :=
  RowIsZero.of_toMatrix h

example (h : IsPivot A i p) : Matrix.IsPivot (DenseMatrix.toMatrix A) i p :=
  h.toMatrix

example (h : Matrix.IsPivot (DenseMatrix.toMatrix A) i p) : IsPivot A i p :=
  IsPivot.of_toMatrix h

end MatrixBridge

private theorem testEchelon_isEchelon : IsEchelonForm testEchelon := by
  apply IsEchelonForm.mk
  · intro i
    fin_cases i <;> simp [RowIsZero, IsPivot, testEchelon, get_ofMatrix_fn]
  · intro i j hij hi
    fin_cases i <;> fin_cases j <;> simp_all [RowIsZero, testEchelon, get_ofMatrix_fn]
  · intro i j p q hij hp hq
    fin_cases i <;> fin_cases j <;> fin_cases p <;> fin_cases q <;>
      simp_all [IsPivot, testEchelon, get_ofMatrix_fn]

example (i : Fin 2) :
    RowIsZero testEchelon i ∨ ∃ p : Fin 2, IsPivot testEchelon i p :=
  testEchelon_isEchelon.row_zero_or_pivot i

example (i j : Fin 2) (hij : i < j) (hi : RowIsZero testEchelon i) :
    RowIsZero testEchelon j :=
  testEchelon_isEchelon.zero_rows_bottom i j hij hi

example (i j p q : Fin 2) (hij : i < j)
    (hp : IsPivot testEchelon i p) (hq : IsPivot testEchelon j q) : p < q :=
  testEchelon_isEchelon.pivots_strictly_increasing i j p q hij hp hq

example : testEchelon.get (1 : Fin 2) (0 : Fin 2) = 0 :=
  testEchelon_isEchelon.pivot_column_zero_below 0 1 0 (by decide)
    (by simp [IsPivot, testEchelon, get_ofMatrix_fn])

private theorem testReducedEchelon_isEchelon : IsEchelonForm testReducedEchelon := by
  apply IsEchelonForm.mk
  · intro i
    fin_cases i <;> simp [RowIsZero, IsPivot, testReducedEchelon, get_ofMatrix_fn]
  · intro i j hij hi
    fin_cases i <;> fin_cases j <;>
      simp_all [RowIsZero, testReducedEchelon, get_ofMatrix_fn]
  · intro i j p q hij hp hq
    fin_cases i <;> fin_cases j <;> fin_cases p <;> fin_cases q <;>
      simp_all [IsPivot, testReducedEchelon, get_ofMatrix_fn]

private theorem testReducedEchelon_isReduced : IsReducedEchelonForm testReducedEchelon := by
  apply IsReducedEchelonForm.mk testReducedEchelon_isEchelon
  · intro i p hp
    fin_cases i <;> fin_cases p <;>
      simp_all [IsPivot, testReducedEchelon, get_ofMatrix_fn]
  · intro i r p hri hp
    fin_cases i <;> fin_cases r <;> fin_cases p <;>
      simp_all [IsPivot, testReducedEchelon, get_ofMatrix_fn]

example : IsEchelonForm testReducedEchelon :=
  testReducedEchelon_isReduced.echelon

example : testReducedEchelon.get (0 : Fin 2) (0 : Fin 2) = 1 :=
  testReducedEchelon_isReduced.pivot_is_one 0 0
    (by simp [IsPivot, testReducedEchelon, get_ofMatrix_fn])

example : testReducedEchelon.get (0 : Fin 2) (1 : Fin 2) = 0 :=
  testReducedEchelon_isReduced.pivot_column_zero_above 1 0 1
    (by decide) (by simp [IsPivot, testReducedEchelon, get_ofMatrix_fn])

end DenseMatrix
