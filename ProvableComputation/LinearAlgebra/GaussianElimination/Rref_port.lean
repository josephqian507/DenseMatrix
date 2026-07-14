import ProvableComputation.LinearAlgebra.DenseMatrix.Defs
import ProvableComputation.LinearAlgebra.GaussianElimination.Defs_port

/-!
# Gaussian Elimination Algorithms

This module implements the executable elimination loops for row-echelon and reduced
row-echelon form. The tuple-valued internal routines are retained for proof convenience,
while the public `Matrix` wrappers return `RowReductionResult`.
-/

open Matrix DenseMatrix

-- universe u

variable {α : Type} [Field α] [DecidableEq α]
variable {m n : ℕ}
variable {hm : m > 0} {hn : n > 0}

namespace GaussianEliminationInternal

-- `eliminateCol` iterates through the matrix row by row, and uses the `replace` operation
-- to set the value in column `pivotCol` of the row to 0.
-- `eliminateCol` calls replace between 0 and `a` times, so this algorithm's certificate
-- should include a `replace` object for each `replace` call in `eliminateCol`
def eliminateColLoopAux
    (pivotRow : Fin m) (pivotCol : Fin n) (pivotVal : α)
    (r : Nat) (cur : DenseMatrix m n α) (steps : List (RowOp m α))
    : (DenseMatrix m n α × List (RowOp m α)) :=
  -- Iterate over each entry in pivotCol.
  if hr : r < m then
    let i : Fin m := ⟨r, hr⟩
    -- Skip over pivotRow.
    if h : i = pivotRow then
      eliminateColLoopAux pivotRow pivotCol pivotVal (r + 1) cur steps
    else
      -- Otherwise, use pivotRow to replace the current row, setting this row's
      -- pivotCol entry to 0.
      let coeff := cur.get i pivotCol
      if coeff ≠ 0 then  -- eliminate unnecessary calls to `replace`
        eliminateColLoopAux pivotRow pivotCol pivotVal (r + 1)
          (_root_.replaceRow cur pivotRow i (-coeff / pivotVal))
          (List.concat steps (.replace pivotRow i (-coeff / pivotVal)))
      else
        eliminateColLoopAux pivotRow pivotCol pivotVal (r + 1) cur steps
  else
    (cur, steps)
termination_by m - r
decreasing_by
  · omega
  · omega
  · omega

def eliminateColLoop
    (pivotRow : Fin m) (pivotCol : Fin n)
    (r : Nat) (cur : DenseMatrix m n α) (steps : List (RowOp m α))
    : (DenseMatrix m n α × List (RowOp m α)) :=
  eliminateColLoopAux pivotRow pivotCol (cur.get pivotRow pivotCol) r cur steps

def eliminateColCore
    (given : DenseMatrix m n α) (pivotRow : Fin m) (pivotCol : Fin n)
    (steps : List (RowOp m α)) (reduced : Bool) : (DenseMatrix m n α × List (RowOp m α)) :=
  if reduced then
    eliminateColLoop pivotRow pivotCol 0 given steps
  else
    eliminateColLoop pivotRow pivotCol pivotRow.val given steps

def rowReductionAux
  (M : DenseMatrix m n α) (row col : Nat) (steps : List (RowOp m α)) (reduced : Bool)
  : (DenseMatrix m n α × List (RowOp m α)) :=
  if hrow : row < m then
    if col < n then
      let pivot_location := checkPivot M row col
      match pivot_location with
      | none => (M, steps)
      | some (pivotRow, pivotCol) =>
        let M1 :=
          if pivotRow.val = row then
            M
          else
            _root_.swapRow M ⟨row, hrow⟩ pivotRow
        let steps := List.concat steps (.swap ⟨row, hrow⟩ pivotRow)
        let pivotVal : α := M1.get ⟨row, hrow⟩ pivotCol
        let M2 :=
          if !reduced || pivotVal = 1 then
            M1
          else
            _root_.scaleRow M1 ⟨row, hrow⟩ (pivotVal)⁻¹
        let steps :=
          if !reduced || pivotVal = 1 then
            steps
          else
            List.concat steps (.factor ⟨row, hrow⟩ (pivotVal)⁻¹)
        let (M3, steps) := eliminateColCore M2 ⟨row, hrow⟩ pivotCol steps reduced
        rowReductionAux M3 (row + 1) (col + 1) steps reduced
    else
      (M, steps)
  else
    (M, steps)

/-- Compute a row-echelon form together with the logged row operations that produce it. -/
def rawRowEchelonForm (given : DenseMatrix m n α)
    : (DenseMatrix m n α × List (RowOp m α)) :=
  rowReductionAux given 0 0 List.nil false

/-- Compute a reduced row-echelon form together with the logged row operations that produce it. -/
def rawReducedRowEchelonForm
 (given : DenseMatrix m n α)
: (DenseMatrix m n α × List (RowOp m α)) :=
  rowReductionAux given 0 0 List.nil true

end GaussianEliminationInternal

namespace DenseMatrix

/-- Structured public wrapper for `GaussianEliminationInternal.rawRowEchelonForm`. -/
def rowEchelonForm
    (given : DenseMatrix m n α) : RowReductionResult m n α :=
  let raw := GaussianEliminationInternal.rawRowEchelonForm given
  { matrix := raw.1, steps := raw.2 }

/-- Structured public wrapper for `GaussianEliminationInternal.rawReducedRowEchelonForm`. -/
def reducedRowEchelonForm
    (given : DenseMatrix m n α) : RowReductionResult m n α :=
  let raw := GaussianEliminationInternal.rawReducedRowEchelonForm given
  { matrix := raw.1, steps := raw.2 }

end DenseMatrix
