import ProvableComputation.linear_algebra.RowEquivalent

variable {R : Type} [Field R] [DecidableEq R]
variable {a : Nat}

namespace ColumnElementary

def swapCol
    (given : Matrix (Fin a) (Fin a) R) (col1 col2 : Fin a) :
    Matrix (Fin a) (Fin a) R :=
  (swapRow given.transpose col1 col2).transpose

def factorCol
    (given : Matrix (Fin a) (Fin a) R) (col : Fin a) (scale : R) :
    Matrix (Fin a) (Fin a) R :=
  (factor given.transpose col scale).transpose

def replaceCol
    (given : Matrix (Fin a) (Fin a) R) (use toReplace : Fin a) (k : R) :
    Matrix (Fin a) (Fin a) R :=
  (replace given.transpose toReplace use k).transpose

omit [DecidableEq R] in
lemma elem_swap_transpose (c1 c2 : Fin a) :
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
lemma elem_factor_transpose (c : Fin a) (s : R) :
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
lemma elem_replace_transpose (use toReplace : Fin a) (k : R) :
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
lemma swapCol_eq_mul_elem
    (M : Matrix (Fin a) (Fin a) R) (c1 c2 : Fin a) :
    swapCol M c1 c2 =
      M * Matrix.elementaryMatrixOfRowOp (.swap c1 c2 : RowOp a R) := by
  let op : RowOp a R := .swap c1 c2
  have h := Matrix.elementaryMatrixOfRowOp_mul_eq_applyRowOp (op := op) (M := M.transpose)
  have ht := congrArg Matrix.transpose h
  simpa [
    op, swapCol, Matrix.applyRowOp, Matrix.transpose_mul, elem_swap_transpose
  ] using
    ht.symm

omit [DecidableEq R] in
lemma factorCol_eq_mul_elem
    (M : Matrix (Fin a) (Fin a) R) (c : Fin a) (s : R) :
    factorCol M c s =
      M * Matrix.elementaryMatrixOfRowOp (.factor c s : RowOp a R) := by
  let op : RowOp a R := .factor c s
  have h := Matrix.elementaryMatrixOfRowOp_mul_eq_applyRowOp (op := op) (M := M.transpose)
  have ht := congrArg Matrix.transpose h
  simpa [
    op, factorCol, Matrix.applyRowOp, Matrix.transpose_mul, elem_factor_transpose
  ] using
    ht.symm

omit [DecidableEq R] in
lemma replaceCol_eq_mul_elem
    (M : Matrix (Fin a) (Fin a) R) (use toReplace : Fin a) (k : R) :
    replaceCol M use toReplace k =
      M * Matrix.elementaryMatrixOfRowOp (.replace use toReplace k : RowOp a R) := by
  let opT : RowOp a R := .replace toReplace use k
  have h := Matrix.elementaryMatrixOfRowOp_mul_eq_applyRowOp (op := opT) (M := M.transpose)
  have ht := congrArg Matrix.transpose h
  simpa [
    opT, replaceCol, Matrix.applyRowOp, Matrix.transpose_mul, elem_replace_transpose
  ] using
    ht.symm

end ColumnElementary
