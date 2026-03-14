import ProvableComputation.linear_algebra.RowEquivalent

-- import Mathlib.Data.Matrix.Basic

variable {R : Type} [Field R] [DecidableEq R]
variable {a : Nat} {b : Nat}
variable {ha : a > 0} {hb : b > 0}

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

private def swapCol (given : squareMatrix a R) (col1 col2 : Fin a) : squareMatrix a R :=
  (swapRow given.transpose col1 col2).transpose

private def factorCol (given : squareMatrix a R) (col : Fin a) (scale : R) : squareMatrix a R :=
  (factor given.transpose col scale).transpose

private def replaceCol
    (given : squareMatrix a R) (use toReplace : Fin a) (k : R) : squareMatrix a R :=
  (replace given.transpose toReplace use k).transpose

omit [DecidableEq R] in
private lemma elem_swap_transpose (c1 c2 : Fin a) :
    (Matrix.elementaryMatrixOfRowOp (.swap c1 c2 : RowOp a R)).transpose =
      Matrix.elementaryMatrixOfRowOp (.swap c1 c2 : RowOp a R) := by
  ext i j
  by_cases hi1 : i = c1
  all_goals
    by_cases hi2 : i = c2
    all_goals
      by_cases hj1 : j = c1
      all_goals
        by_cases hj2 : j = c2
        all_goals
          simp [Matrix.elementaryMatrixOfRowOp, swapRow, Matrix.one_apply, hi1, hi2, hj1, hj2]
          try aesop

omit [DecidableEq R] in
private lemma elem_factor_transpose (c : Fin a) (s : R) :
    (Matrix.elementaryMatrixOfRowOp (.factor c s : RowOp a R)).transpose =
      Matrix.elementaryMatrixOfRowOp (.factor c s : RowOp a R) := by
  ext i j
  by_cases hi : i = c
  all_goals
    by_cases hj : j = c
    all_goals
      simp [Matrix.elementaryMatrixOfRowOp, factor, Matrix.one_apply, hi, hj]
      try aesop

omit [DecidableEq R] in
private lemma elem_replace_transpose (use toReplace : Fin a) (k : R) :
    (Matrix.elementaryMatrixOfRowOp (.replace use toReplace k : RowOp a R)).transpose =
      Matrix.elementaryMatrixOfRowOp (.replace toReplace use k : RowOp a R) := by
  by_cases h : use = toReplace
  case pos =>
    subst h
    simpa [Matrix.elementaryMatrixOfRowOp, replace] using
      (elem_factor_transpose (R := R) (a := a) use (k + 1))
  case neg =>
    ext i j
    by_cases hiUse : i = use
    all_goals
      by_cases hiToReplace : i = toReplace
      all_goals
        by_cases hjUse : j = use
        all_goals
          by_cases hjToReplace : j = toReplace
          all_goals
            simp [Matrix.elementaryMatrixOfRowOp, replace, factor, Matrix.one_apply,
              h, hiUse, hiToReplace, hjUse, hjToReplace]
            try aesop

omit [DecidableEq R] in
private lemma swapCol_eq_mul_elem (M : squareMatrix a R) (c1 c2 : Fin a) :
    swapCol M c1 c2 = M * Matrix.elementaryMatrixOfRowOp (.swap c1 c2 : RowOp a R) := by
  let op : RowOp a R := .swap c1 c2
  have h := Matrix.elementaryMatrixOfRowOp_mul_eq_applyRowOp (op := op) (M := M.transpose)
  have ht := congrArg Matrix.transpose h
  simpa [op, swapCol, Matrix.applyRowOp, Matrix.transpose_mul, elem_swap_transpose] using
    ht.symm

omit [DecidableEq R] in
private lemma factorCol_eq_mul_elem (M : squareMatrix a R) (c : Fin a) (s : R) :
    factorCol M c s = M * Matrix.elementaryMatrixOfRowOp (.factor c s : RowOp a R) := by
  let op : RowOp a R := .factor c s
  have h := Matrix.elementaryMatrixOfRowOp_mul_eq_applyRowOp (op := op) (M := M.transpose)
  have ht := congrArg Matrix.transpose h
  simpa [op, factorCol, Matrix.applyRowOp, Matrix.transpose_mul, elem_factor_transpose] using
    ht.symm

omit [DecidableEq R] in
private lemma replaceCol_eq_mul_elem
    (M : squareMatrix a R) (use toReplace : Fin a) (k : R) :
    replaceCol M use toReplace k =
      M * Matrix.elementaryMatrixOfRowOp (.replace use toReplace k : RowOp a R) := by
  let opT : RowOp a R := .replace toReplace use k
  have h := Matrix.elementaryMatrixOfRowOp_mul_eq_applyRowOp (op := opT) (M := M.transpose)
  have ht := congrArg Matrix.transpose h
  simpa [opT, replaceCol, Matrix.applyRowOp, Matrix.transpose_mul, elem_replace_transpose] using
    ht.symm

private abbrev DenseMatrix (R : Type) := Array (Array R)

private def denseIdentity : DenseMatrix R :=
  (List.finRange a).foldl
    (fun rows i =>
      rows.push <|
        (List.finRange a).foldl
          (fun row j => row.push (if i = j then 1 else 0))
          #[])
    #[]

private def matrixOfDense (M : DenseMatrix R) : squareMatrix a R :=
  Matrix.of fun i j =>
    (M.getD i #[]).getD j 0

private def denseSwap (M : DenseMatrix R) (r1 r2 : Fin a) : DenseMatrix R :=
  let row1 := M.getD r1 #[]
  let row2 := M.getD r2 #[]
  (M.set! r1 row2).set! r2 row1

private def denseFactor (M : DenseMatrix R) (r : Fin a) (s : R) : DenseMatrix R :=
  let row := M.getD r #[]
  M.set! r (row.map (fun elem => elem * s))

private def denseReplace
    (M : DenseMatrix R) (use toReplace : Fin a) (k : R) : DenseMatrix R :=
  if use = toReplace then
    denseFactor M toReplace (k + 1)
  else
    let rowToUse := M.getD use #[]
    let rowToReplace := M.getD toReplace #[]
    M.set! toReplace (rowToReplace.mapIdx fun idx elem => elem + k * (rowToUse.getD idx 0))

private def buildPLFastStep
    (state : Prod (List (Prod (Fin a) (Fin a))) (DenseMatrix R))
    (op : RowOp a R) : Prod (List (Prod (Fin a) (Fin a))) (DenseMatrix R) :=
  let swaps := state.1
  let A := state.2
  match op with
  | .swap i j => (swaps.concat (i, j), denseSwap A i j)
  | .factor row scale => (swaps, denseFactor A row (Inv.inv scale))
  | .replace use toReplace scale => (swaps, denseReplace A use toReplace (-scale))

def buildPL (steps : List (RowOp a R)) : Prod (squareMatrix a R) (squareMatrix a R) :=
  let (swaps, A) := steps.foldl buildPLFastStep ([], denseIdentity (a := a) (R := R))
  let P := swaps.foldl (fun acc ij => denseSwap acc ij.1 ij.2) (denseIdentity (a := a) (R := R))
  let L := swaps.foldl (fun acc ij => denseSwap acc ij.1 ij.2) A
  (matrixOfDense P, matrixOfDense L)

def LUFactorization (M : Matrix (Fin a) (Fin b) R)
    : Prod (squareMatrix a R) (Prod (squareMatrix a R) (Matrix (Fin a) (Fin b) R)) :=
  let (U, steps) := rowEchelonForm M
  let (P, L) := buildPL steps
  (P, (L, U))
