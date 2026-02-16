import ProvableComputation.linear_algebra.Rref
import ProvableComputation.linear_algebra.rref_proofs
import ProvableComputation.linear_algebra.RowEquivalent

variable {R : Type} [Field R] [DecidableEq R]
variable {a : ℕ}
variable {ha : a > 0}

abbrev squareMatrix (a : ℕ) (R : Type) := Matrix (Fin a) (Fin a) R

def buildPL (steps : List (RowOp a R)) (P L : squareMatrix a R)
    : (squareMatrix a R × squareMatrix a R) :=
  match steps with
  | List.nil => (P, L)
  | List.cons a as =>
    match a with
    | .swap _ _ =>
      buildPL as (P * Matrix.elementaryMatrixOfRowOp a) L
    | .factor row scale =>
      let a_inv := RowOp.factor row scale⁻¹
      buildPL as P (L * Matrix.elementaryMatrixOfRowOp a_inv)
    | .replace use toReplace scale =>
      let a_inv := RowOp.replace use toReplace (-scale)
      buildPL as P (L * Matrix.elementaryMatrixOfRowOp a_inv)

def LUFactorization (M : Matrix (Fin a) (Fin a) R)
    : (squareMatrix a R × squareMatrix a R × squareMatrix a R) :=
  let (U, steps) := rowReducedEchelonForm M
  let (P, L) := buildPL steps 1 1
  (P, L, U)



#eval LUFactorization sampleMatrix
#eval (LUFactorization sampleMatrix).1 * (LUFactorization sampleMatrix).2.1 * (LUFactorization sampleMatrix).2.2
