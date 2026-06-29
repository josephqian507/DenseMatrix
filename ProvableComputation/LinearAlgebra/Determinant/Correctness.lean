import ProvableComputation.LinearAlgebra.Determinant.Basic
import ProvableComputation.LinearAlgebra.LU.Correctness

/-!
# Determinant correctness

This file records the public theorem skeletons connecting the executable
determinant algorithms to mathlib's determinant.
-/

namespace Matrix

variable {R : Type} [Field R] [DecidableEq R]
variable {n : Nat}

theorem gaussDet_eq_det (M : Matrix (Fin n) (Fin n) R) :
  Matrix.gaussDet M = M.det := by
    sorry

theorem luDet_eq_det (M : Matrix (Fin n) (Fin n) R) :
  Matrix.luDet M = M.det := by
    sorry

theorem gaussDet_eq_luDet (M : Matrix (Fin n) (Fin n) R) :
  Matrix.gaussDet M = Matrix.luDet M := by
    rw [gaussDet_eq_det, luDet_eq_det]
end Matrix
