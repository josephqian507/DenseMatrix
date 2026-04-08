import ProvableComputation.LinearAlgebra.LU.Defs
import ProvableComputation.LinearAlgebra.GaussianElimination.Elementary
import ProvableComputation.LinearAlgebra.GaussianElimination.Rref

/-!
# LU Basic Algorithm

This module turns the row-operation log produced by Gaussian elimination into permutation
and lower-triangular factors, and exposes the structured public LU-factorization API.
-/

variable {R : Type} [Field R] [DecidableEq R]
variable {a : Nat} {b : Nat}

namespace LUFactorizationInternal

def permutationOfSwaps (swaps : List (Fin a × Fin a)) : squareMatrix a R :=
  swaps.foldl (fun acc ij => ColumnElementary.swapCol acc ij.1 ij.2) 1

def lowerOfSwaps
    (swaps : List (Fin a × Fin a)) (MInv : squareMatrix a R) : squareMatrix a R :=
  swaps.foldl (fun acc ij => swapRow acc ij.1 ij.2) MInv

def buildPLStep
    (state : List (Fin a × Fin a) × squareMatrix a R)
    (op : RowOp a R) : List (Fin a × Fin a) × squareMatrix a R :=
  let swaps := state.1
  let MInv := state.2
  match op with
  | .swap i j => (swaps.concat (i, j), ColumnElementary.swapCol MInv i j)
  | .factor row scale => (swaps, ColumnElementary.factorCol MInv row scale⁻¹)
  | .replace use toReplace scale =>
      if use = toReplace then
        (swaps, ColumnElementary.factorCol MInv toReplace (scale + 1)⁻¹)
      else
        (swaps, ColumnElementary.replaceCol MInv use toReplace (-scale))

end LUFactorizationInternal

/-- Replay a row-operation log into the permutation and lower-triangular bookkeeping factors. -/
def buildPL (steps : List (RowOp a R)) : squareMatrix a R × squareMatrix a R :=
  let (swaps, MInv) :=
    steps.foldl (LUFactorizationInternal.buildPLStep (R := R)) ([], 1)
  let P := LUFactorizationInternal.permutationOfSwaps (R := R) swaps
  let L := LUFactorizationInternal.lowerOfSwaps (R := R) swaps MInv
  (P, L)

/-- Internal tuple-valued LU factorization used by the proof files. -/
def LUFactorization (M : Matrix (Fin a) (Fin b) R) :
    squareMatrix a R × (squareMatrix a R × Matrix (Fin a) (Fin b) R) :=
  let (U, steps) := rowEchelonForm M
  let (P, L) := buildPL steps
  (P, (L, U))

namespace Matrix

/-- Structured public LU factorization. -/
def luFactorization (M : Matrix (Fin a) (Fin b) R) : LUFactors a b R where
  P := (LUFactorization M).1
  L := (LUFactorization M).2.1
  U := (LUFactorization M).2.2

end Matrix
