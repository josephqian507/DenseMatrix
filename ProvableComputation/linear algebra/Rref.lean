import Lean
import Lean.Elab.Tactic
import Qq
import Mathlib.Data.Matrix.Basic

open Matrix

def sampleMatrix : Matrix (Fin 3) (Fin 2) ℕ :=
  ![![1, 2],
  ![0, 4],
  ![5, 6]]

def swapRow {R : Type} [Semiring R] {a b : Nat} (given : Matrix (Fin a) (Fin b) R)
 (row1 row2 : Fin a) : Matrix (Fin a) (Fin b) R :=
  of fun a b =>
    if a = row1 then
      given row2 b
    else if a = row2 then
      given row1 b
    else
      given a b
#eval swapRow sampleMatrix 1 2

def factor {R : Type} [Semiring R] {a b : Nat} (given : Matrix (Fin a) (Fin b) R) (i : Fin a)
  (j : R) : Matrix (Fin a) (Fin b) R :=
  of fun a1 b1 =>
    if a1 = i then
      j * given a1 b1
    else
      given a1 b1
#eval factor sampleMatrix 1 2


def replace {R : Type} [Semiring R] {a b : Nat} (given : Matrix (Fin a) (Fin b) R)
(use toReplace : Fin a) (k : R) : Matrix (Fin a) (Fin b) R:=
  of fun a2 b2 =>
    if a2 = toReplace then
      given toReplace b2 + k * given use b2
    else
      given a2 b2
#eval replace sampleMatrix 1 2 3

def checkPivot {R : Type} [Semiring R] [DecidableEq R] {a b : Nat}
(given : Matrix (Fin a) (Fin b) R) (row : Fin a) (col : Fin b) : Nat :=
  let rec loop1 (r : Nat) : Nat :=
    if h : r < a then
      if given ⟨r, h⟩ col ≠ 0 then
        r
      else
        loop1 (r + 1)
    else
      row
  loop1 row.val
#eval checkPivot sampleMatrix 0 0

def eliminateCol {R : Type} [Semiring R] {a b : Nat}
  (given : Matrix (Fin a) (Fin b) R)
  (pivotRow : Fin a) (pivotCol : Fin b) : Matrix (Fin a) (Fin b) R :=
  let rec go (r : Nat) (cur : Matrix (Fin a) (Fin b) R) : Matrix (Fin a) (Fin b) R :=
    if hr : r < a then
      let i : Fin a := ⟨r, hr⟩
      if h : i = pivotRow then
        go (r + 1) cur
      else
        let coeff := - cur i pivotCol
        let cur' := replace cur pivotRow i coeff
        go (r + 1) cur'
    else
      cur
  go 0 given
#eval eliminateCol sampleMatrix 0 0

def rrefAux {R : Type} [Field R] [DecidableEq R] {a b : Nat}
  (m : Matrix (Fin a) (Fin b) R) (row col : Nat) : Matrix (Fin a) (Fin b) R :=
  -- termination: row or col out of bounds
  if hrow : row < a then
    if hcol : col < b then
      let rowFin : Fin a := ⟨row, hrow⟩
      let colFin : Fin b := ⟨col, hcol⟩

      -- find pivot row index
      let pivotRowNat : Nat := checkPivot m rowFin colFin
      have hpivot : pivotRowNat < a := by
        admit   -- will be proved later

      let pivotRow : Fin a := ⟨pivotRowNat, hpivot⟩

      -- if pivot is zero, no pivot in this column → move to next column
      if hzero : m pivotRow colFin = 0 then
        rrefAux m row (col + 1)
      else
        -- swap pivot row up if needed
        let m1 :=
          if hswap : pivotRow = rowFin then
            m
          else
            swapRow m rowFin pivotRow

        -- scale pivot row so pivot becomes 1
        let pivotVal : R := m1 rowFin colFin
        let m2 : Matrix (Fin a) (Fin b) R :=
          factor m1 rowFin (pivotVal)⁻¹

        -- eliminate all other rows in this pivot column
        let m3 : Matrix (Fin a) (Fin b) R :=
          eliminateCol m2 rowFin colFin

        -- recurse to next row and next column
        rrefAux m3 (row + 1) (col + 1)
    else
      m
  else
    m


<<<<<<< Updated upstream:ProvableComputation/linear algebra/Rref.lean
def rowReducedEchelonForm {R : Type} [Semiring R] [DecidableEq R] {a b : Nat} (given : Matrix (Fin a) (Fin b) R ): Matrix (Fin a) (Fin b) R:=
  let rec loop2 (new_given :  Matrix (Fin a) (Fin b) R ) :  Matrix (Fin a) (Fin b) R  :=
    rrefAux m 0 0
=======
-- def rowReducedEchelonForm {R : Type} [Semiring R] [DecidableEq R] {a b : Nat} (given : Matrix (Fin a) (Fin b) R ): Matrix (Fin a) (Fin b) R:=
--   let rec loop2 (new_given :  Matrix (Fin a) (Fin b) R ) :  Matrix (Fin a) (Fin b) R  :=
--     if checkPivot new_given 0 0 ≠ 0 then
--       swapRow new_given 0 checkPivot 0 0
--     else
>>>>>>> Stashed changes:ProvableComputation/linear_algebra/Rref.lean
