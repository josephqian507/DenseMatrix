import Mathlib.Algebra.Field.Rat
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import ProvableComputation.linear_algebra.LUFactorization
import ProvableComputation.linear_algebra.Rref

variable {R : Type} [Field R] [DecidableEq R]
variable {n : Nat}
variable {hn : n > 0}

open Matrix

def matrix2 : Matrix (Fin 5) (Fin 5) ℚ :=
  ![![3, -2, 5, 1, 4],
    ![1, 6, -3, 2, 0],
    ![4, 0, 2, -1, 5],
    ![-2, 3, 1, 4, -3],
    ![5, 1, -4, 0, 2]]

-- Multilinear, alternating, send identity matrix to 1
def matrix3 : Matrix (Fin 10) (Fin 10) ℚ :=
  ![![ 1,  2, -1,  0,  3,  4, -2,  1,  5,  0],
    ![ 0, -3,  4,  1,  2, -1,  0,  6, -2,  3],
    ![ 5,  1,  0, -2,  4,  3,  1, -1,  0,  2],
    ![-2,  0,  3,  5, -1,  2,  4,  0,  1, -3],
    ![ 4, -1,  2,  0,  6,  1, -3,  5,  0,  2],
    ![ 1,  3,  0, -1,  2,  5,  4, -2,  6,  0],
    ![ 0,  2, -4,  3,  1,  0,  5,  2, -1,  4],
    ![ 3,  0,  1,  4, -2,  6,  0,  1,  2, -1],
    ![-1,  4,  2,  0,  5, -3,  1,  0,  3,  6],
    ![ 2, -2,  5,  1,  0,  4, -1,  3,  0,  1]]


def swapRowDet (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) (d : R) :
  Matrix (Fin n) (Fin n) R × R :=
  if _h : i = j then
    (M, d)
  else
    (swapRow M i j, -d)

def factorDet (M : Matrix (Fin n) (Fin n) R) (i : Fin n) (c : R) (d : R) :
  Matrix (Fin n) (Fin n) R × R :=
  (factor M i c⁻¹, d * c)

private def triangularDet (M : squareMatrix n R) : R :=
  ∏ i : (Fin n), M i i

def gaussDetAux (M : Matrix (Fin n) (Fin n) R) (row : Nat) (d : R) : R :=
  if hrow : row < n then
    match checkPivot M row row with
      | none => 0
      | some (pivotRow, pivotCol) =>
          let rowFin : Fin n := ⟨row, hrow⟩
          let (M, d) := swapRowDet M rowFin pivotRow d
          -- let pivotVal := M1 rowFin pivotCol
          -- let (M2, d2) := factorDet M1 rowFin pivotVal d1
          let (M, _) := eliminateCol M rowFin pivotCol List.nil false
          gaussDetAux M (row + 1) d
  else
    d * triangularDet M

def gaussDet (M : Matrix (Fin n) (Fin n) R) : R :=
  gaussDetAux M 0 1

def LUDet (M : Matrix (Fin n) (Fin n) R) : R :=
  let (P, L, U) := LUFactorization M
  (triangularDet P) * (triangularDet L) * (triangularDet U)
