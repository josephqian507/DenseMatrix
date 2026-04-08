import Mathlib.Algebra.Field.Rat

import ProvableComputation.LinearAlgebra.GaussianElimination.Rref
import ProvableComputation.LinearAlgebra.LU.Defs
import ProvableComputation.LinearAlgebra.LU.Basic

/-!
# Determinant Algorithms

This module contains the executable determinant routines built from Gaussian elimination
and LU factorization, together with namespaced public wrappers on the structured API.
-/

variable {R : Type} [Field R] [DecidableEq R]
variable {n : Nat}
variable {hn : n > 0}

open Matrix

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

/-- Gaussian-elimination determinant computation with explicit swap-sign bookkeeping. -/
def gaussDet (M : Matrix (Fin n) (Fin n) R) : R :=
  gaussDetAux M 0 1

/-- Internal determinant computation via the tuple-valued LU factorization. -/
def LUDet (M : Matrix (Fin n) (Fin n) R) : R :=
  let (P, L, U) := LUFactorization M
  (triangularDet P) * (triangularDet L) * (triangularDet U)

namespace Matrix

/-- Structured public determinant computation via Gaussian elimination. -/
def gaussDet (M : Matrix (Fin n) (Fin n) R) : R :=
  _root_.gaussDet M

/-- Structured public determinant computation via LU factorization. -/
def luDet (M : Matrix (Fin n) (Fin n) R) : R :=
  _root_.LUDet M

end Matrix
