import ProvableComputation.linear_algebra.Rref
import ProvableComputation.linear_algebra.rref_proofs
import ProvableComputation.linear_algebra.RowEquivalent

-- import Mathlib.Data.Matrix.Basic

variable {R : Type} [Field R] [DecidableEq R]
variable {a : Nat}
variable {ha : a > 0}

abbrev squareMatrix (a : Nat) (R : Type) := Matrix (Fin a) (Fin a) R

def sampleMatrix2 : Matrix (Fin 3) (Fin 3) Rat :=
  ![![1, 2, 3],
    ![4, 8, 12],
    ![2, 5, 6]]

def sampleMatrix3 : Matrix (Fin 10) (Fin 10) Rat :=
  ![![9, 8, 6, 9, 7, 4, 6, 8, 4, 7],
    ![27, 30, 22, 34, 29, 17, 23, 31, 20, 24],
    ![36, 86, 61, 106, 134, 66, 77, 100, 97, 64],
    ![9, 212, 153, 327, 658, 236, 272, 307, 384, 215],
    ![27, 24, 22, 61, 168, 52, 74, 65, 71, 79],
    ![0, 180, 124, 244, 387, 198, 214, 258, 304, 150],
    ![9, 26, 20, 71, 152, 148, 193, 181, 247, 169],
    ![27, 78, 58, 133, 262, 184, 307, 296, 753, 237],
    ![27, 30, 54, 267, 1141, 316, 511, 427, 943, 514],
    ![18, 16, 16, 52, 169, 96, 216, 207, 680, 240]]

def sampleMatrix4 : Matrix (Fin 4) (Fin 4) Rat :=
  ![![3, 5, 1, 9],
    ![94, 2, 8, 0],
    ![9, 3, 2, 9],
    ![45, 3, 9, 8]]

private def getLastSafe (l : List (squareMatrix a R)) : squareMatrix a R :=
  if h : l.length = 0 then
    1
  else
    have hl : l.length - 1 < l.length := by
      exact Nat.sub_one_lt h
    l.get <| Fin.mk (l.length - 1) hl

private def setList (l : List (squareMatrix a R)) (op : RowOp a R) (multiply : Bool)
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

#time #eval LUFactorization sampleMatrix
#time #eval (LUFactorization sampleMatrix).1 * (LUFactorization sampleMatrix).2.1 * (LUFactorization sampleMatrix).2.2

#time #eval LUFactorization sampleMatrix2
#time #eval (LUFactorization sampleMatrix2).1 * (LUFactorization sampleMatrix2).2.1 * (LUFactorization sampleMatrix2).2.2

-- #time #eval LUFactorization sampleMatrix4

-- #time #eval LUFactorization sampleMatrix3
-- #time #eval (LUFactorization sampleMatrix3).1 * (LUFactorization sampleMatrix3).2.1 * (LUFactorization sampleMatrix3).2.2
