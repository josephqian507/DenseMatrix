import ProvableComputation.LinearAlgebra.GaussianElimination.Defs

/-!
# Gaussian Elimination Algorithms

This module implements the executable elimination loops for row-echelon and reduced
row-echelon form. The tuple-valued internal routines are retained for proof convenience,
while the public `Matrix` wrappers return `RowReductionResult`.
-/

open Matrix

variable {R : Type} [Field R] [DecidableEq R]
variable {a b : ℕ}
variable {ha : a > 0} {hb : b > 0}

-- `eliminateCol` iterates through the matrix row by row, and uses the `replace` operation
-- to set the value in column `pivotCol` of the row to 0.
-- `eliminateCol` calls replace between 0 and `a` times, so this algorithm's certificate
-- should include a `replace` object for each `replace` call in `eliminateCol`
def eliminateColGoAux
    (pivotRow : Fin a) (pivotCol : Fin b) (pivotVal : R)
    (r : Nat) (cur : Matrix (Fin a) (Fin b) R) (steps : List (RowOp a R))
    : (Matrix (Fin a) (Fin b) R × List (RowOp a R)) :=
  -- Iterate over each entry in pivotCol.
  if hr : r < a then
    let i : Fin a := ⟨r, hr⟩
    -- Skip over pivotRow.
    if h : i = pivotRow then
      eliminateColGoAux pivotRow pivotCol pivotVal (r + 1) cur steps
    else
      -- Otherwise, use pivotRow to replace the current row, setting this row's
      -- pivotCol entry to 0.
      let coeff := cur i pivotCol
      if coeff ≠ 0 then  -- eliminate unnecessary calls to `replace`
        eliminateColGoAux pivotRow pivotCol pivotVal (r + 1)
          (replace cur pivotRow i (-coeff / pivotVal))
          (List.concat steps (.replace pivotRow i (-coeff / pivotVal)))
      else
        eliminateColGoAux pivotRow pivotCol pivotVal (r + 1) cur steps
  else
    (cur, steps)
termination_by a - r
decreasing_by
  · omega
  · omega
  · omega

def eliminateColGo
    (pivotRow : Fin a) (pivotCol : Fin b)
    (r : Nat) (cur : Matrix (Fin a) (Fin b) R) (steps : List (RowOp a R))
    : (Matrix (Fin a) (Fin b) R × List (RowOp a R)) :=
  eliminateColGoAux pivotRow pivotCol (cur pivotRow pivotCol) r cur steps

def eliminateCol
    (given : Matrix (Fin a) (Fin b) R) (pivotRow : Fin a) (pivotCol : Fin b)
    (steps : List (RowOp a R)) (reduced : Bool) : (Matrix (Fin a) (Fin b) R × List (RowOp a R)) :=
  if reduced then
    eliminateColGo pivotRow pivotCol 0 given steps
  else
    eliminateColGo pivotRow pivotCol pivotRow.val given steps

namespace eliminateCol

abbrev go
    (pivotRow : Fin a) (pivotCol : Fin b)
    (r : Nat) (cur : Matrix (Fin a) (Fin b) R) (steps : List (RowOp a R))
    : (Matrix (Fin a) (Fin b) R × List (RowOp a R)) :=
  eliminateColGo pivotRow pivotCol r cur steps

end eliminateCol

def rrefAux
  (m : Matrix (Fin a) (Fin b) R) (row col : Nat) (steps : List (RowOp a R)) (reduced : Bool)
  : (Matrix (Fin a) (Fin b) R × List (RowOp a R)) :=
  if hrow : row < a then
    if col < b then
      let pivot_location := checkPivot m row col
      match pivot_location with
      | none => (m, steps)
      | some (pivotRow, pivotCol) =>
        let m1 :=
          if pivotRow.val = row then
            m
          else
            swapRow m ⟨row, hrow⟩ pivotRow
        let steps := List.concat steps (.swap ⟨row, hrow⟩ pivotRow)
        let pivotVal : R := m1 ⟨row, hrow⟩ pivotCol
        let m2 :=
          if !reduced || pivotVal = 1 then
            m1
          else
            factor m1 ⟨row, hrow⟩ (pivotVal)⁻¹
        let steps :=
          if !reduced || pivotVal = 1 then
            steps
          else
            List.concat steps (.factor ⟨row, hrow⟩ (pivotVal)⁻¹)
        let (m3, steps) := eliminateCol m2 ⟨row, hrow⟩ pivotCol steps reduced
        rrefAux m3 (row + 1) (col + 1) steps reduced
    else
      (m, steps)
  else
    (m, steps)

/-- Compute a row-echelon form together with the logged row operations that produce it. -/
def rowEchelonForm (given : Matrix (Fin a) (Fin b) R)
    : (Matrix (Fin a) (Fin b) R × List (RowOp a R)) :=
  rrefAux given 0 0 List.nil false

/-- Compute a reduced row-echelon form together with the logged row operations that produce it. -/
def reducedRowEchelonForm
 (given : Matrix (Fin a) (Fin b) R)
: (Matrix (Fin a) (Fin b) R × List (RowOp a R)) :=
  rrefAux given 0 0 List.nil true

namespace Matrix

/-- Structured public wrapper for `rowEchelonForm`. -/
def rowEchelonForm
    (given : Matrix (Fin a) (Fin b) R) : RowReductionResult a b R where
  matrix := (_root_.rowEchelonForm given).1
  steps := (_root_.rowEchelonForm given).2

/-- Structured public wrapper for `reducedRowEchelonForm`. -/
def reducedRowEchelonForm
    (given : Matrix (Fin a) (Fin b) R) : RowReductionResult a b R where
  matrix := (_root_.reducedRowEchelonForm given).1
  steps := (_root_.reducedRowEchelonForm given).2

end Matrix
