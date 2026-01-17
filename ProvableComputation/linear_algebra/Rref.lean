-- import Lean
-- import Lean.Elab.Tactic
-- import Qq
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Field.Rat
set_option linter.hashCommand false


open Matrix

def sampleMatrix : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![1, 2, 3],
    ![2, 5, 6],
    ![4, 8, 12]]

variable {R : Type} [Field R] [DecidableEq R]
variable {a b : ℕ}
variable {ha : a > 0} {hb : b > 0}

def swapRow (given : Matrix (Fin a) (Fin b) R)
 (row1 row2 : Fin a) : Matrix (Fin a) (Fin b) R :=
  of fun a b =>
    if a = row1 then
      given row2 b
    else if a = row2 then
      given row1 b
    else
      given a b
#eval swapRow sampleMatrix 1 2

def factor (given : Matrix (Fin a) (Fin b) R) (i : Fin a)
  (j : R) : Matrix (Fin a) (Fin b) R :=
  of fun a1 b1 =>
    if a1 = i then
      j * given a1 b1
    else
      given a1 b1
#eval factor sampleMatrix 1 2

def replace (given : Matrix (Fin a) (Fin b) R)
(use toReplace : Fin a) (k : R) : Matrix (Fin a) (Fin b) R:=
  if use = toReplace then
    factor given toReplace (k+1)
  else
    of fun a2 b2 =>
      if a2 = toReplace then
        given toReplace b2 + k * given use b2
      else
        given a2 b2
#eval replace sampleMatrix 1 2 3
#eval replace sampleMatrix 1 1 3  -- should output the same matrix as the factor call below
#eval factor sampleMatrix 1 4

def checkPivot
  (M : Matrix (Fin a) (Fin b) R)
  (startRow : Nat) (startCol : Nat)
  : Option (Fin a × Fin b) :=

  let rec scanCol (col : Nat) : Option (Fin a × Fin b) :=
    if hcol : col < b then
      -- now scan all rows in this column
      let rec scanRow (row : Nat) : Option (Fin a × Fin b) :=
        if hrow : row < a then
          if M ⟨row, hrow⟩ ⟨col, hcol⟩ ≠ 0 then
            some (⟨row, hrow⟩, ⟨col, hcol⟩)
          else
            scanRow (row + 1)
        else
          none
      match scanRow startRow with
      | some p => some p
      | none   => scanCol (col + 1)
    else
      none
  scanCol startCol

#eval checkPivot sampleMatrix 0 0

-- `eliminateCol` iterates through the matrix row by row, and uses the `replace` operation
-- to set the value in column `pivotCol` of the row to 0.
-- `eliminateCol` calls replace between 0 and `a` times, so this algorithm's certificate
-- should include a `replace` object for each `replace` call in `eliminateCol`
def eliminateCol
  (given : Matrix (Fin a) (Fin b) R)
  (pivotRow : Fin a) (pivotCol : Fin b) : Matrix (Fin a) (Fin b) R :=
  let rec go (r : Nat) (cur : Matrix (Fin a) (Fin b) R) : Matrix (Fin a) (Fin b) R :=
    -- Iterate over each entry in pivotCol
    if hr : r < a then
      let i : Fin a := ⟨r, hr⟩
      -- Skip over pivotRow
      if h : i = pivotRow then
        go (r + 1) cur
      else
        -- Otherwise, use pivotRow to replace the current row, setting this row's
        -- pivotCol entry to 0.
        let coeff := cur i pivotCol
        if coeff ≠ 0 then  -- eliminate unnecessary calls to `replace`
          let cur' := replace cur pivotRow i (-coeff)
          go (r + 1) cur'
        else
          go (r + 1) cur
    else
      cur
  go 0 given
#eval eliminateCol sampleMatrix 0 0

def rrefAux
  (m : Matrix (Fin a) (Fin b) R)
  (row col : Nat) : Matrix (Fin a) (Fin b) R :=
  if hrow : row < a then
    if col < b then

      let pivot_location := checkPivot m row col
      match pivot_location with
      | none => m
      | some (pivotRow, pivotCol) =>
        let m1 :=
          if pivotRow.val = row then
            m
          else
            swapRow m ⟨row, hrow⟩ pivotRow

        let pivotVal : R := m1 ⟨row, hrow⟩ pivotCol
        let m2 := factor m1 ⟨row, hrow⟩ (pivotVal)⁻¹
        let m3 := eliminateCol m2 ⟨row, hrow⟩ pivotCol

        rrefAux m3 (row + 1) (col + 1)
    else
      m
  else
    m


def rowReducedEchelonForm
 (given : Matrix (Fin a) (Fin b) R)
: Matrix (Fin a) (Fin b) R:=
  rrefAux given 0 0

#eval rowReducedEchelonForm sampleMatrix
