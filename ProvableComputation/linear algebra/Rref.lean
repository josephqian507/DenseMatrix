import Lean
import Lean.Elab.Tactic
import Qq
import Mathlib.Data.Matrix.Basic

open Matrix

def sampleMatrix : Matrix (Fin 3) (Fin 2) ℕ :=
  ![![0, 0],
  ![0, 4],
  ![0, 6]]

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
    if h1 : r1 < b then
      checkPivot given ⟨r1, h1⟩
    else if h : r < a then
      if given ⟨r, h⟩ col ≠ 0 then
        r
      else
        loop1 (r + 1)

def rowReducedEchelonForm {R : Type} [Semiring R] [DecidableEq R] {a b : Nat}
(given : Matrix (Fin a) (Fin b) R ): Matrix (Fin a) (Fin b) R:=
  if a = 0 || b == 0 then
    new_given
  else if checkPivot new_given 0 0 ≠ 0 then
    swapRow new_given 0 checkPivot 0 0
  else
