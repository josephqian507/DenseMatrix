/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
import ProvableComputation.LinearAlgebra.DenseMatrix.Defs
import ProvableComputation.LinearAlgebra.Echelon

/-!
Dense matrix echelon
-/

namespace DenseMatrix

universe u

variable {R : Type u} [Field R]

def IsEchelonForm {m n : Nat} (A : DenseMatrix m n R) : Prop :=
  Matrix.IsEchelonForm (toMatrix A)

def IsReducedEchelonForm {m n : Nat} (A : DenseMatrix m n R) : Prop :=
  Matrix.IsReducedEchelonForm (toMatrix A)

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

end DenseMatrix
