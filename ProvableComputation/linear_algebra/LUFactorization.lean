import Mathlib.LinearAlgebra.Matrix.Block

import ProvableComputation.linear_algebra.ColumnElementary
import ProvableComputation.linear_algebra.Rref

variable {R : Type} [Field R] [DecidableEq R]
variable {a : Nat} {b : Nat}

abbrev squareMatrix (a : Nat) (R : Type) := Matrix (Fin a) (Fin a) R

def IsUnitLowerTriangular (L : squareMatrix a R) : Prop :=
  L.BlockTriangular OrderDual.toDual ∧ ∀ i : Fin a, L i i = 1

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

def buildPL (steps : List (RowOp a R)) : squareMatrix a R × squareMatrix a R :=
  let (swaps, MInv) :=
    steps.foldl (LUFactorizationInternal.buildPLStep (R := R)) ([], 1)
  let P := LUFactorizationInternal.permutationOfSwaps (R := R) swaps
  let L := LUFactorizationInternal.lowerOfSwaps (R := R) swaps MInv
  (P, L)

def LUFactorization (M : Matrix (Fin a) (Fin b) R) :
    squareMatrix a R × (squareMatrix a R × Matrix (Fin a) (Fin b) R) :=
  let (U, steps) := rowEchelonForm M
  let (P, L) := buildPL steps
  (P, (L, U))
