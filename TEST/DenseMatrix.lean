import ProvableComputation.LinearAlgebra.DenseMatrix.Defs

/-!
# Dense matrix smoke tests

These examples exercise the executable DenseMatrix operations on small matrices.
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

private def smokeA23Swapped : Matrix (Fin 2) (Fin 3) Nat :=
  ![![4, 5, 6],
    ![1, 2, 3]]

private def smokeA23ScaledRow0 : Matrix (Fin 2) (Fin 3) Nat :=
  ![![3, 6, 9],
    ![4, 5, 6]]

private def smokeA23ReplacedRow1 : Matrix (Fin 2) (Fin 3) Nat :=
  ![![1, 2, 3],
    ![6, 9, 12]]

set_option linter.style.nativeDecide false in
example : toMatrix (mul (ofMatrix smokeA23) (ofMatrix smokeB32)) = smokeA23 * smokeB32 := by
  native_decide

set_option linter.style.nativeDecide false in
example : toMatrix (swapRow (ofMatrix smokeA23) (0 : Fin 2) (1 : Fin 2)) = smokeA23Swapped := by
  native_decide

set_option linter.style.nativeDecide false in
example : toMatrix (swapRow (ofMatrix smokeA23) (0 : Fin 2) (0 : Fin 2)) = smokeA23 := by
  native_decide

set_option linter.style.nativeDecide false in
example : toMatrix (scaleRow (ofMatrix smokeA23) (0 : Fin 2) 3) = smokeA23ScaledRow0 := by
  native_decide

set_option linter.style.nativeDecide false in
example : toMatrix (replaceRow (ofMatrix smokeA23) (0 : Fin 2) (1 : Fin 2) 2) =
    smokeA23ReplacedRow1 := by
  native_decide

set_option linter.style.nativeDecide false in
example : toMatrix (replaceRow (ofMatrix smokeA23) (0 : Fin 2) (0 : Fin 2) 2) =
    smokeA23ScaledRow0 := by
  native_decide

end DenseMatrix
