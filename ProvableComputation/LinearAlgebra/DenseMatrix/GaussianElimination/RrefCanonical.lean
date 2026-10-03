/-
Copyright (c) 2026 Joseph Qian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Qian, Junye Ji, Dhruv Bhatia
-/

import ProvableComputation.LinearAlgebra.DenseMatrix.GaussianElimination.RrefCorrectness
import ProvableComputation.LinearAlgebra.Matrix.RrefUniqueness

/-!
# Canonical Reduced Row-Echelon Form

This module connects the executable `DenseMatrix` reduced-row-echelon algorithm to the
generic uniqueness theory for mathlib matrices. Generic RREF uniqueness remains in
`ProvableComputation.LinearAlgebra.Matrix.RrefUniqueness`.
-/

universe v

variable {α : Type v} [Field α] [DecidableEq α]

open DenseMatrix

namespace Matrix

/-- `A` is the representative of `B` selected by the executable reduced-row-echelon algorithm. -/
def IsCanonicalRrefOf {m n : Nat}
    (A B : Matrix (Fin m) (Fin n) α) : Prop :=
  A = (reducedRowEchelonForm (ofMatrix B)).matrix.toMatrix

/-- The output selected by the executable algorithm is canonical for its input. -/
lemma isCanonicalRrefOf_reducedRowEchelonForm {m n : Nat}
    (B : Matrix (Fin m) (Fin n) α) :
    (reducedRowEchelonForm (ofMatrix B)).matrix.toMatrix.IsCanonicalRrefOf B :=
  rfl

/-- Two canonical representatives of the same matrix are equal. -/
theorem IsCanonicalRrefOf.unique {m n : Nat}
    {A A' B : Matrix (Fin m) (Fin n) α}
    (hA : A.IsCanonicalRrefOf B)
    (hA' : A'.IsCanonicalRrefOf B) :
    A = A' := by
  exact hA.trans hA'.symm

/-- A canonical representative has the complete semantic reduced-row-echelon guarantee. -/
lemma IsCanonicalRrefOf.isReducedRowEchelonOf {m n : Nat}
    {A B : Matrix (Fin m) (Fin n) α}
    (hA : A.IsCanonicalRrefOf B) :
    A.IsReducedRowEchelonOf B := by
  rcases hA with rfl
  simpa using DenseMatrix.reducedRowEchelonForm_isReducedRowEchelonOf (ofMatrix B)

/-- A canonical representative is in reduced row-echelon form. -/
lemma IsCanonicalRrefOf.reduced {m n : Nat}
    {A B : Matrix (Fin m) (Fin n) α}
    (hA : A.IsCanonicalRrefOf B) :
    A.IsReducedRowEchelon :=
  hA.isReducedRowEchelonOf.isReducedRowEchelon

/-- Every semantic reduced representative equals the representative selected by the algorithm. -/
lemma IsReducedRowEchelonOf.canonical {m n : Nat}
    {A B : Matrix (Fin m) (Fin n) α} (h : A.IsReducedRowEchelonOf B) :
    A = (reducedRowEchelonForm (ofMatrix B)).matrix.toMatrix := by
  have hCanonical :
      (reducedRowEchelonForm (ofMatrix B)).matrix.toMatrix.IsReducedRowEchelonOf B := by
    simpa using DenseMatrix.reducedRowEchelonForm_isReducedRowEchelonOf (ofMatrix B)
  exact h.unique hCanonical

end Matrix
