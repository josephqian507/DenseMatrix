/-
Copyright (c) 2026 Provable Computation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Provable Computation contributors
-/

import ProvableComputation.LinearAlgebra.DenseMatrix.Elementary
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

namespace GaussianEliminationInternal

-- `eliminateCol` iterates through the matrix row by row, and uses the `replace` operation
-- to set the value in column `pivotCol` of the row to 0.
-- `eliminateCol` calls replace between 0 and `a` times, so this algorithm's certificate
-- should include a `replace` object for each `replace` call in `eliminateCol`
def eliminateColLoopAux
    (pivotRow : Fin a) (pivotCol : Fin b) (pivotVal : R)
    (r : Nat) (cur : Matrix (Fin a) (Fin b) R) (steps : List (RowOp a R))
    : (Matrix (Fin a) (Fin b) R × List (RowOp a R)) :=
  -- Iterate over each entry in pivotCol.
  if hr : r < a then
    let i : Fin a := ⟨r, hr⟩
    -- Skip over pivotRow.
    if h : i = pivotRow then
      eliminateColLoopAux pivotRow pivotCol pivotVal (r + 1) cur steps
    else
      -- Otherwise, use pivotRow to replace the current row, setting this row's
      -- pivotCol entry to 0.
      let coeff := cur i pivotCol
      if coeff ≠ 0 then  -- eliminate unnecessary calls to `replace`
        eliminateColLoopAux pivotRow pivotCol pivotVal (r + 1)
          (replace cur pivotRow i (-coeff / pivotVal))
          (List.concat steps (.replace pivotRow i (-coeff / pivotVal)))
      else
        eliminateColLoopAux pivotRow pivotCol pivotVal (r + 1) cur steps
  else
    (cur, steps)
termination_by a - r
decreasing_by all_goals omega

def eliminateColLoop
    (pivotRow : Fin a) (pivotCol : Fin b)
    (r : Nat) (cur : Matrix (Fin a) (Fin b) R) (steps : List (RowOp a R))
    : (Matrix (Fin a) (Fin b) R × List (RowOp a R)) :=
  eliminateColLoopAux pivotRow pivotCol (cur pivotRow pivotCol) r cur steps

def eliminateColCore
    (given : Matrix (Fin a) (Fin b) R) (pivotRow : Fin a) (pivotCol : Fin b)
    (steps : List (RowOp a R)) (reduced : Bool) : (Matrix (Fin a) (Fin b) R × List (RowOp a R)) :=
  if reduced then
    eliminateColLoop pivotRow pivotCol 0 given steps
  else
    eliminateColLoop pivotRow pivotCol pivotRow.val given steps

def rowReductionAux
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
        let (m3, steps) := eliminateColCore m2 ⟨row, hrow⟩ pivotCol steps reduced
        rowReductionAux m3 (row + 1) (col + 1) steps reduced
    else
      (m, steps)
  else
    (m, steps)

/-- Compute a row-echelon form together with the logged row operations that produce it. -/
def rawRowEchelonForm (given : Matrix (Fin a) (Fin b) R)
    : (Matrix (Fin a) (Fin b) R × List (RowOp a R)) :=
  rowReductionAux given 0 0 List.nil false

/-- Compute a reduced row-echelon form together with the logged row operations that produce it. -/
def rawReducedRowEchelonForm
 (given : Matrix (Fin a) (Fin b) R)
: (Matrix (Fin a) (Fin b) R × List (RowOp a R)) :=
  rowReductionAux given 0 0 List.nil true

end GaussianEliminationInternal

namespace DenseMatrix

/-- Dense-native column elimination loop. Mirrors the Matrix reference control flow. -/
def eliminateColLoopAux
    (pivotRow : Fin a) (pivotCol : Fin b) (pivotVal : R)
    (r : Nat) (cur : DenseMatrix a b R) (steps : List (RowOp a R))
    : (DenseMatrix a b R × List (RowOp a R)) :=
  if hr : r < a then
    let i : Fin a := ⟨r, hr⟩
    if h : i = pivotRow then
      eliminateColLoopAux pivotRow pivotCol pivotVal (r + 1) cur steps
    else
      let coeff := cur.get i pivotCol
      if coeff ≠ 0 then
        eliminateColLoopAux pivotRow pivotCol pivotVal (r + 1)
          (replace cur pivotRow i (-coeff / pivotVal))
          (List.concat steps (.replace pivotRow i (-coeff / pivotVal)))
      else
        eliminateColLoopAux pivotRow pivotCol pivotVal (r + 1) cur steps
  else
    (cur, steps)
termination_by a - r
decreasing_by all_goals omega

/-- Dense-native column elimination entry point. -/
def eliminateColLoop
    (pivotRow : Fin a) (pivotCol : Fin b)
    (r : Nat) (cur : DenseMatrix a b R) (steps : List (RowOp a R))
    : (DenseMatrix a b R × List (RowOp a R)) :=
  eliminateColLoopAux pivotRow pivotCol (cur.get pivotRow pivotCol) r cur steps

/-- Dense-native choice between REF and RREF elimination ranges. -/
def eliminateColCore
    (given : DenseMatrix a b R) (pivotRow : Fin a) (pivotCol : Fin b)
    (steps : List (RowOp a R)) (reduced : Bool) : (DenseMatrix a b R × List (RowOp a R)) :=
  if reduced then
    eliminateColLoop pivotRow pivotCol 0 given steps
  else
    eliminateColLoop pivotRow pivotCol pivotRow.val given steps

/--
Dense-native row-reduction loop. The branch structure intentionally matches the
Matrix reference.
-/
def rowReductionAux
  (m : DenseMatrix a b R) (row col : Nat) (steps : List (RowOp a R)) (reduced : Bool)
  : (DenseMatrix a b R × List (RowOp a R)) :=
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
        let pivotVal : R := m1.get ⟨row, hrow⟩ pivotCol
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
        let (m3, steps) := eliminateColCore m2 ⟨row, hrow⟩ pivotCol steps reduced
        rowReductionAux m3 (row + 1) (col + 1) steps reduced
    else
      (m, steps)
  else
    (m, steps)

/-- Dense-native row-echelon implementation. -/
def rawRowEchelonForm
    (given : DenseMatrix a b R) : (DenseMatrix a b R × List (RowOp a R)) :=
  rowReductionAux given 0 0 List.nil false

/-- Dense-native reduced-row-echelon implementation. -/
def rawReducedRowEchelonForm
    (given : DenseMatrix a b R) : (DenseMatrix a b R × List (RowOp a R)) :=
  rowReductionAux given 0 0 List.nil true

/-
The dense implementation is intentionally a behavioral clone of the Matrix
reference loop.  The bridge lemmas below prove that cloning at every recursive
boundary, including the step log, so the correctness files can continue to talk
about the established Matrix algorithms.
-/
private theorem eliminateColLoopAux_toMatrix
    (pivotRow : Fin a) (pivotCol : Fin b) (pivotVal : R)
    (r : Nat) (cur : DenseMatrix a b R) (steps : List (RowOp a R)) :
    ((eliminateColLoopAux pivotRow pivotCol pivotVal r cur steps).1.toMatrix,
        (eliminateColLoopAux pivotRow pivotCol pivotVal r cur steps).2) =
      GaussianEliminationInternal.eliminateColLoopAux
        pivotRow pivotCol pivotVal r cur.toMatrix steps := by
  by_cases hr : r < a
  · let i : Fin a := ⟨r, hr⟩
    by_cases hrow : i = pivotRow
    · rw [eliminateColLoopAux, GaussianEliminationInternal.eliminateColLoopAux]
      rw [dif_pos hr, dif_pos hr]
      simpa [i, hrow] using
        eliminateColLoopAux_toMatrix
        (pivotRow := pivotRow) (pivotCol := pivotCol) (pivotVal := pivotVal)
        (r := r + 1) (cur := cur) (steps := steps)
    · by_cases hcoeff : cur.get i pivotCol ≠ 0
      · have hcoeffMatrix : cur.toMatrix i pivotCol ≠ 0 := by
          simpa [DenseMatrix.toMatrix] using hcoeff
        rw [eliminateColLoopAux, GaussianEliminationInternal.eliminateColLoopAux]
        rw [dif_pos hr, dif_pos hr]
        simpa [i, hrow, hcoeff, hcoeffMatrix, DenseMatrix.toMatrix_replace] using
          eliminateColLoopAux_toMatrix
            (pivotRow := pivotRow) (pivotCol := pivotCol) (pivotVal := pivotVal)
            (r := r + 1)
            (cur := replace cur pivotRow i (-(cur.get i pivotCol) / pivotVal))
            (steps := List.concat steps (.replace pivotRow i (-(cur.get i pivotCol) / pivotVal)))
      · have hcoeffMatrix : ¬ cur.toMatrix i pivotCol ≠ 0 := by
          simpa [DenseMatrix.toMatrix] using hcoeff
        rw [eliminateColLoopAux, GaussianEliminationInternal.eliminateColLoopAux]
        rw [dif_pos hr, dif_pos hr]
        simpa [i, hrow, hcoeff, hcoeffMatrix] using
          eliminateColLoopAux_toMatrix
          (pivotRow := pivotRow) (pivotCol := pivotCol) (pivotVal := pivotVal)
          (r := r + 1) (cur := cur) (steps := steps)
  · rw [eliminateColLoopAux, GaussianEliminationInternal.eliminateColLoopAux]
    rw [dif_neg hr, dif_neg hr]
termination_by a - r
decreasing_by all_goals omega

private theorem eliminateColLoop_toMatrix
    (pivotRow : Fin a) (pivotCol : Fin b)
    (r : Nat) (cur : DenseMatrix a b R) (steps : List (RowOp a R)) :
    ((eliminateColLoop pivotRow pivotCol r cur steps).1.toMatrix,
        (eliminateColLoop pivotRow pivotCol r cur steps).2) =
      GaussianEliminationInternal.eliminateColLoop pivotRow pivotCol r cur.toMatrix steps := by
  simpa [eliminateColLoop, GaussianEliminationInternal.eliminateColLoop, DenseMatrix.toMatrix] using
    eliminateColLoopAux_toMatrix
      (pivotRow := pivotRow) (pivotCol := pivotCol) (pivotVal := cur.get pivotRow pivotCol)
      (r := r) (cur := cur) (steps := steps)

private theorem eliminateColCore_toMatrix
    (given : DenseMatrix a b R) (pivotRow : Fin a) (pivotCol : Fin b)
    (steps : List (RowOp a R)) (reduced : Bool) :
    ((eliminateColCore given pivotRow pivotCol steps reduced).1.toMatrix,
        (eliminateColCore given pivotRow pivotCol steps reduced).2) =
      GaussianEliminationInternal.eliminateColCore
        given.toMatrix pivotRow pivotCol steps reduced := by
  cases reduced <;>
    simp [eliminateColCore, GaussianEliminationInternal.eliminateColCore, eliminateColLoop_toMatrix]

private theorem rowReductionAux_toMatrix
    (m : DenseMatrix a b R) (row col : Nat) (steps : List (RowOp a R)) (reduced : Bool) :
    ((rowReductionAux m row col steps reduced).1.toMatrix,
        (rowReductionAux m row col steps reduced).2) =
      GaussianEliminationInternal.rowReductionAux m.toMatrix row col steps reduced := by
  by_cases hrow : row < a
  · by_cases hcol : col < b
    · cases hcp : checkPivot m row col with
      | none =>
          have hcpMatrix : _root_.checkPivot m.toMatrix row col = none := by
            simpa [DenseMatrix.checkPivot_eq_matrix] using hcp
          rw [rowReductionAux, GaussianEliminationInternal.rowReductionAux]
          rw [dif_pos hrow, dif_pos hrow, if_pos hcol, if_pos hcol, hcp, hcpMatrix]
      | some pivot =>
          rcases pivot with ⟨pivotRow, pivotCol⟩
          have hcpMatrix :
              _root_.checkPivot m.toMatrix row col = some (pivotRow, pivotCol) := by
            simpa [DenseMatrix.checkPivot_eq_matrix] using hcp
          rw [rowReductionAux, GaussianEliminationInternal.rowReductionAux]
          rw [dif_pos hrow, dif_pos hrow, if_pos hcol, if_pos hcol, hcp, hcpMatrix]
          let rowFin : Fin a := ⟨row, hrow⟩
          let m1 : DenseMatrix a b R :=
            if pivotRow.val = row then m else swapRow m rowFin pivotRow
          let steps1 : List (RowOp a R) := List.concat steps (.swap rowFin pivotRow)
          let pivotVal : R := m1.get rowFin pivotCol
          let m2 : DenseMatrix a b R :=
            if !reduced || pivotVal = 1 then m1 else factor m1 rowFin pivotVal⁻¹
          let steps2 : List (RowOp a R) :=
            if !reduced || pivotVal = 1 then
              steps1
            else
              List.concat steps1 (.factor rowFin pivotVal⁻¹)
          let m1M : Matrix (Fin a) (Fin b) R :=
            if pivotRow.val = row then m.toMatrix else _root_.swapRow m.toMatrix rowFin pivotRow
          let pivotValM : R := m1M rowFin pivotCol
          let m2M : Matrix (Fin a) (Fin b) R :=
            if !reduced || pivotValM = 1 then m1M else _root_.factor m1M rowFin pivotValM⁻¹
          let steps2M : List (RowOp a R) :=
            if !reduced || pivotValM = 1 then
              steps1
            else
              List.concat steps1 (.factor rowFin pivotValM⁻¹)
          have hm1 : m1.toMatrix = m1M := by
            by_cases hpivotRow : pivotRow.val = row <;>
              simp [m1, m1M, hpivotRow, DenseMatrix.toMatrix_swapRow]
          have hpivotVal : pivotVal = pivotValM := by
            dsimp [pivotVal, pivotValM]
            rw [← DenseMatrix.toMatrix_apply m1 rowFin pivotCol, hm1]
          have hm2 : m2.toMatrix = m2M := by
            by_cases hscale : !reduced || pivotVal = 1
            · have hscaleM : !reduced || pivotValM = 1 := by
                simpa [hpivotVal] using hscale
              simp [m2, m2M, hscale, hscaleM, hm1]
            · have hscaleM : ¬ (!reduced || pivotValM = 1) := by
                simpa [hpivotVal] using hscale
              simp [m2, m2M, hscaleM, hm1, hpivotVal,
                DenseMatrix.toMatrix_factor]
          have hsteps2 : steps2 = steps2M := by
            by_cases hscale : !reduced || pivotVal = 1
            · have hscaleM : !reduced || pivotValM = 1 := by
                simpa [hpivotVal] using hscale
              simp [steps2, steps2M, hscale, hscaleM]
            · have hscaleM : ¬ (!reduced || pivotValM = 1) := by
                simpa [hpivotVal] using hscale
              simp [steps2, steps2M, hscaleM, hpivotVal]
          let denseElim := eliminateColCore m2 rowFin pivotCol steps2 reduced
          have hRec :=
            rowReductionAux_toMatrix (m := denseElim.1) (row := row + 1) (col := col + 1)
              (steps := denseElim.2) (reduced := reduced)
          have hElim :=
            eliminateColCore_toMatrix (given := m2) (pivotRow := rowFin) (pivotCol := pivotCol)
              (steps := steps2) (reduced := reduced)
          have hElim' :
              (denseElim.1.toMatrix, denseElim.2) =
                GaussianEliminationInternal.eliminateColCore
                  m2M rowFin pivotCol steps2M reduced := by
            simpa [denseElim, hm2, hsteps2] using hElim
          have hElimCongr :=
            congrArg
              (fun x =>
                GaussianEliminationInternal.rowReductionAux x.1 (row + 1) (col + 1) x.2
                  reduced)
              hElim'
          have hCombined := Eq.trans hRec hElimCongr
          simpa [rowFin, m1, steps1, pivotVal, m2, steps2, m1M, pivotValM, m2M,
            steps2M, denseElim] using hCombined
    · rw [rowReductionAux, GaussianEliminationInternal.rowReductionAux]
      rw [dif_pos hrow, dif_pos hrow, if_neg hcol, if_neg hcol]
  · rw [rowReductionAux, GaussianEliminationInternal.rowReductionAux]
    rw [dif_neg hrow, dif_neg hrow]
termination_by a - row
decreasing_by omega

@[simp]
theorem rawRowEchelonForm_toMatrix
    (given : DenseMatrix a b R) :
    ((rawRowEchelonForm given).1.toMatrix, (rawRowEchelonForm given).2) =
      GaussianEliminationInternal.rawRowEchelonForm given.toMatrix := by
  simpa [rawRowEchelonForm, GaussianEliminationInternal.rawRowEchelonForm] using
    rowReductionAux_toMatrix (m := given) (row := 0) (col := 0)
      (steps := List.nil) (reduced := false)

@[simp]
theorem rawReducedRowEchelonForm_toMatrix
    (given : DenseMatrix a b R) :
    ((rawReducedRowEchelonForm given).1.toMatrix, (rawReducedRowEchelonForm given).2) =
      GaussianEliminationInternal.rawReducedRowEchelonForm given.toMatrix := by
  simpa [rawReducedRowEchelonForm, GaussianEliminationInternal.rawReducedRowEchelonForm] using
    rowReductionAux_toMatrix (m := given) (row := 0) (col := 0)
      (steps := List.nil) (reduced := true)

/-- Structured DenseMatrix row-echelon output. -/
def rowEchelonForm
    (given : DenseMatrix a b R) : DenseMatrix.RowReductionResult a b R :=
  let raw := rawRowEchelonForm given
  { matrix := raw.1, steps := raw.2 }

/-- Structured DenseMatrix reduced-row-echelon output. -/
def reducedRowEchelonForm
    (given : DenseMatrix a b R) : DenseMatrix.RowReductionResult a b R :=
  let raw := rawReducedRowEchelonForm given
  { matrix := raw.1, steps := raw.2 }

@[simp]
theorem rowEchelonForm_toMatrix
    (given : DenseMatrix a b R) :
    ((rowEchelonForm given).matrix.toMatrix, (rowEchelonForm given).steps) =
      GaussianEliminationInternal.rawRowEchelonForm given.toMatrix := by
  simp [rowEchelonForm]

@[simp]
theorem rowEchelonForm_matrix_toMatrix
    (given : DenseMatrix a b R) :
    (rowEchelonForm given).matrix.toMatrix =
      (GaussianEliminationInternal.rawRowEchelonForm given.toMatrix).1 := by
  have h := rowEchelonForm_toMatrix (given := given)
  exact congrArg Prod.fst h

@[simp]
theorem rowEchelonForm_steps
    (given : DenseMatrix a b R) :
    (rowEchelonForm given).steps =
      (GaussianEliminationInternal.rawRowEchelonForm given.toMatrix).2 := by
  have h := rowEchelonForm_toMatrix (given := given)
  exact congrArg Prod.snd h

@[simp]
theorem reducedRowEchelonForm_toMatrix
    (given : DenseMatrix a b R) :
    ((reducedRowEchelonForm given).matrix.toMatrix, (reducedRowEchelonForm given).steps) =
      GaussianEliminationInternal.rawReducedRowEchelonForm given.toMatrix := by
  simp [reducedRowEchelonForm]

@[simp]
theorem reducedRowEchelonForm_matrix_toMatrix
    (given : DenseMatrix a b R) :
    (reducedRowEchelonForm given).matrix.toMatrix =
      (GaussianEliminationInternal.rawReducedRowEchelonForm given.toMatrix).1 := by
  have h := reducedRowEchelonForm_toMatrix (given := given)
  exact congrArg Prod.fst h

@[simp]
theorem reducedRowEchelonForm_steps
    (given : DenseMatrix a b R) :
    (reducedRowEchelonForm given).steps =
      (GaussianEliminationInternal.rawReducedRowEchelonForm given.toMatrix).2 := by
  have h := reducedRowEchelonForm_toMatrix (given := given)
  exact congrArg Prod.snd h

end DenseMatrix

namespace Matrix

/-
The public Matrix wrappers now enter through `DenseMatrix.ofMatrix` and convert
the result back.  This gives callers the same API and proof-facing result type
while benchmarking the row-major backend in ordinary Matrix workflows.
-/
/-- Structured public wrapper routed through the DenseMatrix executable surface. -/
def rowEchelonForm
    (given : Matrix (Fin a) (Fin b) R) : RowReductionResult a b R :=
  let raw := DenseMatrix.rowEchelonForm (DenseMatrix.ofMatrix given)
  { matrix := raw.matrix.toMatrix, steps := raw.steps }

/-- Structured public wrapper routed through the DenseMatrix executable surface. -/
def reducedRowEchelonForm
    (given : Matrix (Fin a) (Fin b) R) : RowReductionResult a b R :=
  let raw := DenseMatrix.reducedRowEchelonForm (DenseMatrix.ofMatrix given)
  { matrix := raw.matrix.toMatrix, steps := raw.steps }

end Matrix
