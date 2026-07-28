import ProvableComputation.LinearAlgebra.Determinant.Basic

/-!
# Determinant smoke tests

These examples exercise small executable determinant cases against mathlib's determinant.
-/

namespace Matrix

private def swap2 : Matrix (Fin 2) (Fin 2) Rat :=
  Matrix.of fun i j =>
    if (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) then 1 else 0

#guard Matrix.det swap2 = (-1 : Rat)

#guard Matrix.gaussDet swap2 = (-1 : Rat)

#guard Matrix.luDet swap2 = (-1 : Rat)

end Matrix
