/-
Copyright (c) 2026 Provable Computation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Provable Computation contributors
-/

import ProvableComputation.LinearAlgebra.DenseMatrix.Echelon
import ProvableComputation.LinearAlgebra.DenseMatrix.GaussianElimination.Rref
import ProvableComputation.LinearAlgebra.GaussianElimination.RrefUniqueness

/-!
# Dense RREF semantics and uniqueness

Dense row equivalence and echelon-representative predicates are stated through
the exact `toMatrix` view. The Matrix uniqueness theorem therefore gives native
`DenseMatrix` equality without duplicating its pivot proof.

This module does not assert that the executable Dense RREF is row-equivalent or
reduced; those claims require the separate Dense correctness layer.
-/

namespace DenseMatrix

variable {R : Type} [Field R]
variable {m n : Nat}

/-- Dense row equivalence through the function-backed specification view. -/
def RowEquivalent (A B : DenseMatrix m n R) : Prop :=
  Matrix.RowEquivalent A.toMatrix B.toMatrix

/-- Dense row equivalence is reflexive. -/
theorem RowEquivalent.refl (A : DenseMatrix m n R) : RowEquivalent A A :=
  Matrix.RowEquivalent.refl A.toMatrix

/-- Dense row equivalence is symmetric. -/
theorem RowEquivalent.symm {A B : DenseMatrix m n R}
    (h : RowEquivalent A B) : RowEquivalent B A :=
  Matrix.RowEquivalent.symm h

/-- Dense row equivalence is transitive. -/
theorem RowEquivalent.trans {A B C : DenseMatrix m n R}
    (hAB : RowEquivalent A B) (hBC : RowEquivalent B C) : RowEquivalent A C :=
  Matrix.RowEquivalent.trans hAB hBC

/-- Dense row equivalence as a setoid. -/
instance rowEquivalentSetoid : Setoid (DenseMatrix m n R) where
  r := RowEquivalent
  iseqv := ⟨RowEquivalent.refl, RowEquivalent.symm, RowEquivalent.trans⟩

/-- `B` is a dense echelon-form representative of `A`. -/
def IsEchelonFormOf (A B : DenseMatrix m n R) : Prop :=
  RowEquivalent A B ∧ DenseMatrix.IsEchelonForm B

/-- Extract row equivalence from a dense echelon representative. -/
theorem IsEchelonFormOf.rowEquivalent {A B : DenseMatrix m n R}
    (h : IsEchelonFormOf A B) : RowEquivalent A B :=
  h.1

/-- Extract echelon form from a dense echelon representative. -/
theorem IsEchelonFormOf.echelon {A B : DenseMatrix m n R}
    (h : IsEchelonFormOf A B) : DenseMatrix.IsEchelonForm B :=
  h.2

/-- Package row equivalence and echelon form as a dense echelon representative. -/
theorem isEchelonFormOf_mk {A B : DenseMatrix m n R}
    (hRow : RowEquivalent A B) (hEch : DenseMatrix.IsEchelonForm B) :
    IsEchelonFormOf A B :=
  ⟨hRow, hEch⟩

/-- `B` is a dense reduced-echelon representative of `A`. -/
def IsReducedEchelonFormOf (A B : DenseMatrix m n R) : Prop :=
  RowEquivalent A B ∧ DenseMatrix.IsReducedEchelonForm B

/-- Extract row equivalence from a dense reduced-echelon representative. -/
theorem IsReducedEchelonFormOf.rowEquivalent {A B : DenseMatrix m n R}
    (h : IsReducedEchelonFormOf A B) : RowEquivalent A B :=
  h.1

/-- Extract reduced echelon form from a dense reduced-echelon representative. -/
theorem IsReducedEchelonFormOf.reduced {A B : DenseMatrix m n R}
    (h : IsReducedEchelonFormOf A B) : DenseMatrix.IsReducedEchelonForm B :=
  h.2

/-- A dense reduced-echelon representative is also an echelon representative. -/
theorem IsReducedEchelonFormOf.echelon {A B : DenseMatrix m n R}
    (h : IsReducedEchelonFormOf A B) : IsEchelonFormOf A B :=
  ⟨h.rowEquivalent, h.reduced.echelon⟩

/-- Package row equivalence and reduced echelon form as a dense representative. -/
theorem isReducedEchelonFormOf_mk {A B : DenseMatrix m n R}
    (hRow : RowEquivalent A B) (hRed : DenseMatrix.IsReducedEchelonForm B) :
    IsReducedEchelonFormOf A B :=
  ⟨hRow, hRed⟩

/-- Any two dense reduced-echelon representatives of one source are equal. -/
theorem IsReducedEchelonFormOf.unique {A B B' : DenseMatrix m n R}
    (hB : IsReducedEchelonFormOf A B)
    (hB' : IsReducedEchelonFormOf A B') : B = B' := by
  classical
  have hMatrix : B.toMatrix = B'.toMatrix := by
    apply Matrix.IsReducedEchelonFormOf.unique
    · exact ⟨hB.rowEquivalent, hB.reduced.toMatrix⟩
    · exact ⟨hB'.rowEquivalent, hB'.reduced.toMatrix⟩
  calc
    B = DenseMatrix.ofMatrix B.toMatrix := (DenseMatrix.ofMatrix_toMatrix B).symm
    _ = DenseMatrix.ofMatrix B'.toMatrix := congrArg DenseMatrix.ofMatrix hMatrix
    _ = B' := DenseMatrix.ofMatrix_toMatrix B'

section Canonical

variable [DecidableEq R]

/-- A canonical dense RREF is, definitionally, the selected executable output. -/
def IsCanonicalRrefOf (A B : DenseMatrix m n R) : Prop :=
  B = (DenseMatrix.reducedRowEchelonForm A).matrix

/-- The executable output is canonical by definition. -/
theorem isCanonicalRrefOf_reducedRowEchelonForm (A : DenseMatrix m n R) :
    IsCanonicalRrefOf A (DenseMatrix.reducedRowEchelonForm A).matrix :=
  rfl

/-- Alias matching the computed-output naming used by the Matrix API. -/
theorem reducedRowEchelonForm_isCanonicalRrefOf (A : DenseMatrix m n R) :
    IsCanonicalRrefOf A (DenseMatrix.reducedRowEchelonForm A).matrix :=
  isCanonicalRrefOf_reducedRowEchelonForm A

/-- Canonical dense RREF representatives are unique by definition. -/
theorem IsCanonicalRrefOf.unique {A B B' : DenseMatrix m n R}
    (hB : IsCanonicalRrefOf A B) (hB' : IsCanonicalRrefOf A B') : B = B' := by
  rw [hB, hB']

end Canonical

/-- Dense row-equivalent matrices have the same homogeneous solution set in Matrix view. -/
theorem RowEquivalent.mul_eq_zero_iff {A B : DenseMatrix m n R}
    (hAB : RowEquivalent A B)
    (x : Matrix (Fin n) (Fin 1) R) :
    A.toMatrix * x = 0 ↔ B.toMatrix * x = 0 :=
  Matrix.RowEquivalent.mul_eq_zero_iff hAB x

/--
Dense matrices row-equivalent to a common source have the same homogeneous
solution set in Matrix view.
-/
theorem rowEquivalent_common_source_mul_eq_zero_iff
    {A B B' : DenseMatrix m n R}
    (hAB : RowEquivalent A B)
    (hAB' : RowEquivalent A B')
    (x : Matrix (Fin n) (Fin 1) R) :
    B.toMatrix * x = 0 ↔ B'.toMatrix * x = 0 :=
  Matrix.rowEquivalent_common_source_mul_eq_zero_iff hAB hAB' x

/-- Semantic stage-2 specification of dense RREF uniqueness. -/
def RrefUniquenessSemanticGoal (A : DenseMatrix m n R) : Prop :=
  ∀ {B B' : DenseMatrix m n R},
    IsReducedEchelonFormOf A B →
    IsReducedEchelonFormOf A B' →
    B = B'

/-- The semantic stage-2 specification holds for dense matrices. -/
theorem rrefUniquenessSemanticGoal_holds (A : DenseMatrix m n R) :
    RrefUniquenessSemanticGoal A := by
  intro B B' hB hB'
  exact hB.unique hB'

end DenseMatrix
