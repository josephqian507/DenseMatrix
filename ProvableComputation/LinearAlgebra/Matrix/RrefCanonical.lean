/-
Copyright (c) 2026 Joseph Qian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Qian, Junye Ji, Dhruv Bhatia
-/

import ProvableComputation.LinearAlgebra.DenseMatrix.GaussianElimination.Rref
import ProvableComputation.LinearAlgebra.Matrix.RrefUniqueness
import ProvableComputation.LinearAlgebra.Matrix.Echelon
import Mathlib.LinearAlgebra.Matrix.Echelon.Basic

universe v

variable {m n : Type*}
variable {α : Type v} {A : Matrix m n α}

variable [Field α] [DecidableEq α]

open DenseMatrix

namespace Matrix

/--
Canonical representative predicate.

This is intentionally algorithmic: `B` must be definitionally the selected
output of `GaussianEliminationInternal.rawReducedRowEchelonForm`. It is not the semantic "any
reduced representative" notion.
-/
def IsCanonicalRrefOf {m n : Nat}
    (A B : Matrix (Fin m) (Fin n) α) : Prop :=
  A = (reducedRowEchelonForm (ofMatrix B)).matrix.toMatrix

/-- The algorithm output is canonical for its own input matrix. -/
lemma isCanonicalRrefOf_reducedRowEchelonForm {m n : Nat}
    (A : Matrix (Fin m) (Fin n) α) :
    (reducedRowEchelonForm (ofMatrix A)).matrix.toMatrix.IsCanonicalRrefOf A :=
  rfl

/--
Uniqueness at the canonical level is definitional.

If both `B` and `B'` are stated to be the same algorithm output of `A`,
they are equal by rewriting.
-/
theorem IsCanonicalRrefOf.unique {m n : Nat}
    {A A' B : Matrix (Fin m) (Fin n) α}
    (hA : A.IsCanonicalRrefOf B)
    (hA' : A'.IsCanonicalRrefOf B) :
    A = A' := by
  calc
    A = (reducedRowEchelonForm (ofMatrix B)).matrix.toMatrix := hA
    _ = A' := hA'.symm

/--
Canonical representative implies reduced form.

This connects the algorithm-chosen representative to semantic properties by
reusing the canonical structured wrapper theorem.
-/
lemma IsCanonicalRrefOf.reduced {m n : Nat}
    {A B : Matrix (Fin m) (Fin n) α}
    (hA : A.IsCanonicalRrefOf B) :
    B.IsReducedRowEchelon := by
  rcases hA with rfl
  simpa [Matrix.IsReducedRowEchelon] using
    A.reducedRowEchelonForm_isReducedEchelonForm

/--
Semantic-to-canonical corollary.

Any semantic representative `B` of `A` equals the canonical algorithm output.
-/
lemma IsReducedRowEchelonOf.canonical {m n : Nat}
    {A B : Matrix (Fin m) (Fin n) α} (h : A.IsReducedRowEchelonOf B) :
    A = (reducedRowEchelonForm (ofMatrix B)).matrix.toMatrix := by
  exact IsReducedRowEchelonOf.unique h (reducedRowEchelonForm_isReducedRowEchelonOf B)

end Matrix
