import ProvableComputation.LinearAlgebra.DenseMatrix.GaussianElimination.Elementary

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

private def smokeA23Transpose : Matrix (Fin 3) (Fin 2) Nat :=
  ![![1, 4],
    ![2, 5],
    ![3, 6]]

example : toMatrix (ofMatrix smokeA20) = smokeA20 := by simp

example : toMatrix (ofMatrix smokeB03) = smokeB03 := by simp

#guard toMatrix (mul (ofMatrix smokeA23) (ofMatrix smokeB32)) = smokeA23 * smokeB32

#guard toMatrix (transpose (ofMatrix smokeA23)) = smokeA23Transpose

#guard toMatrix (swapRow (ofMatrix smokeA23) (0 : Fin 2) (1 : Fin 2)) = smokeA23Swapped

#guard toMatrix (swapRow (ofMatrix smokeA23) (0 : Fin 2) (0 : Fin 2)) = smokeA23

#guard toMatrix (scaleRow (ofMatrix smokeA23) (0 : Fin 2) 3) = smokeA23ScaledRow0

#guard toMatrix (replaceRow (ofMatrix smokeA23) (0 : Fin 2) (1 : Fin 2) 2) =
    smokeA23ReplacedRow1

#guard toMatrix (replaceRow (ofMatrix smokeA23) (0 : Fin 2) (0 : Fin 2) 2) =
    smokeA23ScaledRow0

#guard s!"{of (m := 3) (n := 3) fun i j => i.val + j.val}" =
    "![![0, 1, 2], ![1, 2, 3], ![2, 3, 4]]"

end DenseMatrix
