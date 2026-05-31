/-
Copyright (c) 2026 Provable Computation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Provable Computation contributors
-/

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import ProvableComputation.LinearAlgebra.DenseMatrix.Defs
import ProvableComputation.LinearAlgebra.DenseMatrix.Elementary
import ProvableComputation.LinearAlgebra.Determinant.Correctness

/-!
# DenseMatrix executable checks

These tests keep the Vector-backed dense representation aligned with mathlib's
function-backed `Matrix` operations on small closed examples.
-/

namespace DenseMatrix

private def smokeA23 : Matrix (Fin 2) (Fin 3) Nat :=
  ![![1, 2, 3],
    ![4, 5, 6]]

private def smokeB32 : Matrix (Fin 3) (Fin 2) Nat :=
  ![![7, 8],
    ![9, 10],
    ![11, 12]]

private def smokeA20 : Matrix (Fin 2) (Fin 0) Nat :=
  Matrix.of fun _ j => Fin.elim0 j

private def smokeB03 : Matrix (Fin 0) (Fin 3) Nat :=
  Matrix.of fun i _ => Fin.elim0 i

/-
The next fixtures cover the scalar families used by the dense backend:
`Rat` for elimination and determinant code, `Int` for pointwise arithmetic, and
`Nat` for constructor/access smoke tests.
-/
private def ratA22 : Matrix (Fin 2) (Fin 2) Rat :=
  ![![1 / 2, -3 / 4],
    ![5 / 6, 7 / 8]]

private def intA23 : Matrix (Fin 2) (Fin 3) Int :=
  ![![1, -2, 3],
    ![-4, 0, 5]]

private def intB23 : Matrix (Fin 2) (Fin 3) Int :=
  ![![-6, 7, 8],
    ![9, -10, 11]]

private def intB32 : Matrix (Fin 3) (Fin 2) Int :=
  ![![2, -1],
    ![0, 3],
    ![-4, 5]]

private def natDenseA23 : DenseMatrix 2 3 Nat :=
  ofMatrix smokeA23

/-
Basic conversion and storage checks make sure the row-major representation is
extensionally identical to `Matrix`, including empty dimensions.  These are the
cheap tests that catch mistakes in flatten/unflatten arithmetic before larger
algorithm checks fail.
-/
example : toMatrix (ofMatrix smokeA23) = smokeA23 := by
  simp

example : toMatrix (ofMatrix smokeA20) = smokeA20 := by
  simp

example : toMatrix (ofMatrix smokeB03) = smokeB03 := by
  simp

example : toMatrix (ofMatrix (toMatrix natDenseA23)) = toMatrix natDenseA23 := by
  simp

example : natDenseA23.get ⟨1, by decide⟩ ⟨2, by decide⟩ = 6 := by
  rfl

example : natDenseA23.get! 1 2 = 6 := by
  rfl

/-
Dense arithmetic tests exercise the public executable operations and rely on
the bridge lemmas rather than expanding array internals.  That keeps the test
suite aligned with the API a downstream proof or benchmark would actually use.
-/
example :
    toMatrix (DenseMatrix.mul (ofMatrix smokeA23) (ofMatrix smokeB32)) =
      smokeA23 * smokeB32 := by
  simp

example :
    toMatrix (DenseMatrix.add (ofMatrix intA23) (ofMatrix intB23)) =
      intA23 + intB23 := by
  simp

example :
    toMatrix (DenseMatrix.smul (-3 : Int) (ofMatrix intA23)) =
      Matrix.of (fun i j => (-3 : Int) * intA23 i j) := by
  rw [toMatrix_smul, toMatrix_ofMatrix]

example :
    toMatrix (DenseMatrix.transpose (ofMatrix intA23)) =
      intA23.transpose := by
  simp

example :
    toMatrix (DenseMatrix.mul (ofMatrix intA23) (ofMatrix intB32)) =
      intA23 * intB32 := by
  simp

example : toMatrix (natDenseA23.set ⟨0, by decide⟩ ⟨1, by decide⟩ 99)
    = Matrix.of ![![1, 99, 3],
      ![4, 5, 6]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

example : toMatrix (natDenseA23.set! 1 0 88)
    = Matrix.of ![![1, 2, 3],
      ![88, 5, 6]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-
Elementary operation tests pin the DenseMatrix row/column operations to the
legacy Matrix definitions.  These examples are small, but they cover the exact
operations replayed by row reduction and LU bookkeeping.
-/
example : toMatrix (swapRow (ofMatrix ratA22) 0 1) = _root_.swapRow ratA22 0 1 := by
  simp

example : toMatrix (factor (ofMatrix ratA22) 0 (3 : Rat)) =
    _root_.factor ratA22 0 (3 : Rat) := by
  simp

example : toMatrix (replace (ofMatrix ratA22) 0 1 (2 : Rat)) =
    _root_.replace ratA22 0 1 (2 : Rat) := by
  simp

example : toMatrix (DenseMatrix.swapCol (ofMatrix ratA22) 0 1) =
    (_root_.swapRow ratA22.transpose 0 1).transpose := by
  simp

example : toMatrix (DenseMatrix.factorCol (ofMatrix ratA22) 0 (3 : Rat)) =
    (_root_.factor ratA22.transpose 0 (3 : Rat)).transpose := by
  simp

example : toMatrix (DenseMatrix.replaceCol (ofMatrix ratA22) 0 1 (2 : Rat)) =
    (_root_.replace ratA22.transpose 1 0 (2 : Rat)).transpose := by
  simp

/-
Row-reduction bridge tests assert equality of both the resulting matrix and the
operation log.  The log matters because determinant and LU correctness consume
those recorded operations, not just the echelon matrix.
-/
example :
    ((DenseMatrix.rawRowEchelonForm (ofMatrix ratA22)).1.toMatrix,
      (DenseMatrix.rawRowEchelonForm (ofMatrix ratA22)).2) =
        GaussianEliminationInternal.rawRowEchelonForm ratA22 := by
  simp

example :
    ((DenseMatrix.rawReducedRowEchelonForm (ofMatrix ratA22)).1.toMatrix,
      (DenseMatrix.rawReducedRowEchelonForm (ofMatrix ratA22)).2) =
        GaussianEliminationInternal.rawReducedRowEchelonForm ratA22 := by
  simp

/-
Determinant and LU fixtures cover a swap sign, a singular matrix, a nonsingular
matrix, and a rectangular LU case.  Together they exercise the row-operation log
path as well as the structured factorization output.
-/
private def swapDet22 : Matrix (Fin 2) (Fin 2) Rat :=
  ![![0, 1],
    ![1, 0]]

private def singularDet33 : Matrix (Fin 3) (Fin 3) Rat :=
  ![![1, 2, 3],
    ![2, 4, 6],
    ![7, 8, 9]]

private def nonsingularDet33 : Matrix (Fin 3) (Fin 3) Rat :=
  ![![2, -1, 3],
    ![0, 5, 4],
    ![7, 1, -2]]

private def rectangularLU23 : Matrix (Fin 2) (Fin 3) Rat :=
  ![![1, 2, 3],
    ![4, 5, 6]]

/-
The determinant examples check both public Matrix wrappers and DenseMatrix
wrappers against `Matrix.det`, then pin small executable values for the separate
Gaussian-elimination and LU determinant paths.
-/
example : Matrix.luDet swapDet22 = -1 := by
  rw [Matrix.luDet_eq_det]
  norm_num [swapDet22, Matrix.det_fin_two]

example : DenseMatrix.luDet (ofMatrix swapDet22) = -1 := by
  rw [DenseMatrix.luDet_eq_det]
  norm_num [swapDet22, Matrix.det_fin_two]

example : Matrix.gaussDet swapDet22 = swapDet22.det := by
  exact Matrix.gaussDet_eq_det swapDet22

example : Matrix.luDet swapDet22 = swapDet22.det := by
  exact Matrix.luDet_eq_det swapDet22

example : Matrix.gaussDet singularDet33 = singularDet33.det := by
  exact Matrix.gaussDet_eq_det singularDet33

example : Matrix.luDet singularDet33 = singularDet33.det := by
  exact Matrix.luDet_eq_det singularDet33

example : Matrix.gaussDet nonsingularDet33 = nonsingularDet33.det := by
  exact Matrix.gaussDet_eq_det nonsingularDet33

example : Matrix.luDet nonsingularDet33 = nonsingularDet33.det := by
  exact Matrix.luDet_eq_det nonsingularDet33

example : DenseMatrix.gaussDet (ofMatrix swapDet22) = swapDet22.det := by
  simpa using DenseMatrix.gaussDet_eq_det (ofMatrix swapDet22)

example : DenseMatrix.luDet (ofMatrix swapDet22) = swapDet22.det := by
  simpa using DenseMatrix.luDet_eq_det (ofMatrix swapDet22)

section DeterminantExecutableChecks

set_option linter.style.nativeDecide false

example : Matrix.gaussDet singularDet33 = 0 := by
  native_decide

example : Matrix.luDet singularDet33 = 0 := by
  native_decide

example : Matrix.gaussDet nonsingularDet33 = -161 := by
  native_decide

example : Matrix.luDet nonsingularDet33 = -161 := by
  native_decide

example : DenseMatrix.gaussDet (ofMatrix nonsingularDet33) = -161 := by
  native_decide

example : DenseMatrix.luDet (ofMatrix nonsingularDet33) = -161 := by
  native_decide

end DeterminantExecutableChecks

/-
The final LU tests verify the dense factorization bridge and then use the public
Matrix reconstruction theorem on a rectangular input, matching the API that a
downstream caller would use in a proof.
-/
example :
    let lu := DenseMatrix.luFactorization (ofMatrix rectangularLU23)
    (lu.P.toMatrix, lu.L.toMatrix, lu.U.toMatrix) =
      let raw := LUFactorizationInternal.rawFactorization rectangularLU23
      (raw.1, raw.2.1, raw.2.2) := by
  simp

example :
    let lu := Matrix.luFactorization rectangularLU23
    lu.P * lu.L * lu.U = rectangularLU23 := by
  exact Matrix.luFactorization_reconstruct rectangularLU23

end DenseMatrix
