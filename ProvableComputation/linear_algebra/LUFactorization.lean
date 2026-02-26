import ProvableComputation.linear_algebra.Rref
import ProvableComputation.linear_algebra.rref_proofs
import ProvableComputation.linear_algebra.RowEquivalent

variable {R : Type} [Field R] [DecidableEq R]
variable {a : ℕ}
variable {ha : a > 0}

abbrev squareMatrix (a : ℕ) (R : Type) := Matrix (Fin a) (Fin a) R

def sampleMatrix2 : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![1, 2, 3],
    ![4, 8, 12],
    ![2, 5, 6]]

def getLastSafe (l : List (squareMatrix a R)) : squareMatrix a R :=
  if h : l.length = 0 then
    1
  else
    have hl : l.length - 1 < l.length := by exact Nat.sub_one_lt h
    l.get ⟨l.length - 1, hl⟩

def setList (l : List (squareMatrix a R)) (op : RowOp a R) (multiply : Bool)
    : List (squareMatrix a R) :=
  if multiply then
    l.set (l.length - 1)
      ((getLastSafe l) * (Matrix.elementaryMatrixOfRowOp op))
  else
    l.concat (Matrix.elementaryMatrixOfRowOp op)

/-- Build lists of length n for P and L such that l[0]l[1]...l[n-2]l[n-1]U = M, where even indices
    are permutations (elements of P) and odd indices are lower triangular products of elementary
    matrices (elements of L).
    This requires the row reduction algorithm to add row swap steps to the step list even when no
    rows are actually swapped (e.g. .swap 3 3) -/
def buildPLHelper (steps : List (RowOp a R)) (PList l : List (squareMatrix a R))
    (multiply : Bool)
    : List (squareMatrix a R) × squareMatrix a R :=
  match steps with
  | List.nil => (PList, l.foldl (· * ·) 1)
  | List.cons op ops =>
    match op with
    | .swap _ _ =>
      buildPLHelper ops (PList.concat (Matrix.elementaryMatrixOfRowOp op))
        (l.concat (Matrix.elementaryMatrixOfRowOp op)) false
    | .factor row scale =>
      let op_inv := RowOp.factor row scale⁻¹
      let l' := setList l op_inv multiply
      buildPLHelper ops PList l' true
    | .replace use toReplace scale =>
      let op_inv := RowOp.replace use toReplace (-scale)
      let l' := setList l op_inv multiply
      buildPLHelper ops PList l' true

def buildPL (steps : List (RowOp a R)) : (squareMatrix a R × squareMatrix a R) :=
  let (PList, A) := buildPLHelper steps [] [] false
  let P := PList.foldl (· * ·) 1
  let Λ := (PList.reverse.foldl (· * ·) 1) * A
  (P, Λ)

def LUFactorization (M : Matrix (Fin a) (Fin a) R)
    : (squareMatrix a R × squareMatrix a R × squareMatrix a R) :=
  let (U, steps) := rowEchelonForm M
  let (P, L) := buildPL steps
  (P, L, U)

#eval LUFactorization sampleMatrix
#eval (LUFactorization sampleMatrix).1 * (LUFactorization sampleMatrix).2.1 * (LUFactorization sampleMatrix).2.2

#eval LUFactorization sampleMatrix2
#eval (LUFactorization sampleMatrix2).1 * (LUFactorization sampleMatrix2).2.1 * (LUFactorization sampleMatrix2).2.2
