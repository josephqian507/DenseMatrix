import ProvableComputation.LinearAlgebra.DenseMatrix.GaussianElimination.RrefUniqueness

/-!
# Dense RREF uniqueness tests

This file is a minimal declaration fixture for the algorithm-independent uniqueness port.
-/

namespace DenseMatrix

variable {R : Type} [Field R]
variable {m n : Nat}

example {A B B' : DenseMatrix m n R}
    (hB : IsReducedEchelonFormOf A B)
    (hB' : IsReducedEchelonFormOf A B') : B = B' :=
  hB.unique hB'

example {A B B' : DenseMatrix 0 0 Rat}
    (hB : IsReducedEchelonFormOf A B)
    (hB' : IsReducedEchelonFormOf A B') : B = B' :=
  hB.unique hB'

#print axioms IsReducedEchelonFormOf.unique

end DenseMatrix
