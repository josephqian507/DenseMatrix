# AI Instructions

## Organization Rules

* `ProvableComputation.LinearAlgebra.Matrix.ElementaryRowOperations` contains code from a PR
we made, which (at the time of this writing) has not been released in an official Lean
release. If there is a new release including our code, update the mathlib version and edit
any files that import this file to account for this change.
* Do not write any theory for DenseMatrices. Instead, write the theory for mathlib Matrices
(if it doesn't already exist in mathlib) and put it in
`ProvableComputation.LinearAlgebra.Matrix.Echelon`. If any of these theorems should be added
to existing files in mathlib, then make a note of that.

## Task 1: Refactor RrefCorrectness

### Subtask 1.1: Row Equivalence

* The first group of proofs in `ProvableComputation.LinearAlgebra.DenseMatrix.GaussianElimination.RrefCorrectness`
(that is, `ref_proof`, `rref_proof`, and the relevant helper functions) is supposed to prove
that the output of our row reduction algorithm is row equivalent to the input matrix.
* Currently, it uses the language `A * x = 0 <-> B * x = 0`. Please refactor these proofs so
that they are consistent with mathlib's formalization of matrix-vector multiplication, i.e.
`mulVec A x = 0 <-> mulVec B x = 0`. Also use mathlib theorems about `mulVec` if they can be
used to simplify the proofs.
* Modify `ref_proof` and `rref_proof` so that they prove that the two matrices in question
are row equivalent rather than stopping at equal kernels. The type signature of `ref_proof`
should be `RowEquivalent M.toMatrix (rowEchelonForm M).1.toMatrix` (similar for `rref_proof`).
* In particular, this proof retain its current structure of proving that each row operation
and helper function (i.e. eliminateCol) preserves the null space of the input matrix.
* IMPORTANT NOTE: There is already a proof of this in the same file (which has been commented
out), but I prefer the proof method that is used in the version that is not commented out.
Your task is to make the minimal adjustments necessary to turn the uncommented version of the
proof into a proof of the statement in question.

### Subtask 1.2: IsRowEchelon/IsReducedRowEchelon

* Next, we want to show that converting the DenseMatrix returned by our algorithm to a Matrix
always gives a (reduced) row echelon form Matrix, i.e.
`IsRowEchelon (rowEchelonForm M).1.toMatrix` (similar for `IsReducedRowEchelon`).

### Subtask 1.3: IsRowEchelonOf/IsReducedRowEchelonOf

* `A.IsRowEchelonOf B` is a structure containing the proofs `RowEquivalent A B` and
`IsRowEchelon A`.
* Combine the results from 1.1 and 1.2 to prove
`(rowEchelonForm M).1.toMatrix.IsRowEchelonOf M`.
* Similar for `IsReducedRowEchelonOf`.