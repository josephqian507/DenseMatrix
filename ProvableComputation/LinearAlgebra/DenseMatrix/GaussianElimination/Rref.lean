/-
Copyright (c) 2026 Joseph Qian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Qian, Junye Ji, Dhruv Bhatia
-/

import ProvableComputation.LinearAlgebra.DenseMatrix.Basic
import ProvableComputation.LinearAlgebra.DenseMatrix.GaussianElimination.Basic

/-!
# Gaussian Elimination Algorithms

This module implements the executable elimination loops for row-echelon and reduced
row-echelon form. The tuple-valued internal routines are retained for proof convenience,
while the public `DenseMatrix` wrappers return `RowReductionResult`.
-/

universe u

open Matrix DenseMatrix

variable {α : Type u} [Field α] [DecidableEq α]
variable {m n : ℕ}
variable {hm : m > 0} {hn : n > 0}

namespace DenseMatrix.GaussianEliminationInternal

/--
Find the first nonzero pivot entry at or below `startRow` and at or to the right of
`startCol`.
-/
def checkPivot
    (M : DenseMatrix m n α)
    (startRow startCol : Nat) :
    Option (Fin m × Fin n) :=
  let rec scanCol (col : Nat) : Option (Fin m × Fin n) :=
    if hcol : col < n then
      let rec scanRow (row : Nat) : Option (Fin m × Fin n) :=
        if hrow : row < m then
          if M.get ⟨row, hrow⟩ ⟨col, hcol⟩ ≠ 0 then
            some (⟨row, hrow⟩, ⟨col, hcol⟩)
          else
            scanRow (row + 1)
        else
          none
      match scanRow startRow with
      | some p => some p
      | none => scanCol (col + 1)
    else
      none
  scanCol startCol

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
          (DenseMatrix.replaceRow cur pivotRow i (-coeff / pivotVal))
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

/--
`eliminateCol` iterates through the matrix row by row, and uses the `replace` operation
to set the value in column `pivotCol` of the row to 0.
-/
def eliminateCol
    (givenMatrix : DenseMatrix m n α) (pivotRow : Fin m) (pivotCol : Fin n)
    (steps : List (RowOp m α)) (reduced : Bool) : (DenseMatrix m n α × List (RowOp m α)) :=
  if reduced then
    eliminateColLoop pivotRow pivotCol 0 givenMatrix steps
  else
    eliminateColLoop pivotRow pivotCol pivotRow.val givenMatrix steps

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
            DenseMatrix.swapRow M ⟨row, hrow⟩ pivotRow
        let steps :=
          if pivotRow.val = row then
            steps
          else
            List.concat steps (.swap ⟨row, hrow⟩ pivotRow)
        let pivotVal : α := M1.get ⟨row, hrow⟩ pivotCol
        let M2 :=
          if !reduced || pivotVal = 1 then
            M1
          else
            DenseMatrix.scaleRow M1 ⟨row, hrow⟩ (pivotVal)⁻¹
        let steps :=
          if !reduced || pivotVal = 1 then
            steps
          else
            List.concat steps (.scale ⟨row, hrow⟩ (pivotVal)⁻¹)
        let (M3, steps) := eliminateCol M2 ⟨row, hrow⟩ pivotCol steps reduced
        rowReductionAux M3 (row + 1) (col + 1) steps reduced
    else
      (M, steps)
  else
    (M, steps)

end DenseMatrix.GaussianEliminationInternal

namespace DenseMatrix

/--
Computes the row echelon form of a matrix and records the row operations used to get the
result.
-/
def rowEchelonForm
    (givenMatrix : DenseMatrix m n α) : RowReductionResult m n α :=
  let result := GaussianEliminationInternal.rowReductionAux givenMatrix 0 0 List.nil false
  { matrix := result.1, steps := result.2 }

/--
Computes the reduced row echelon form of a matrix and records the row operations used to get the
result.
-/
def reducedRowEchelonForm
    (givenMatrix : DenseMatrix m n α) : RowReductionResult m n α :=
  let result := GaussianEliminationInternal.rowReductionAux givenMatrix 0 0 List.nil true
  { matrix := result.1, steps := result.2 }

end DenseMatrix
