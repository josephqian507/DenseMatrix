import ProvableComputation.linear_algebra.RowEquivalent
import ProvableComputation.linear_algebra.IsInReducedEchelonFormProofs

namespace Matrix

variable {R : Type} [Field R]

/-- `B` is an RREF representative of `A`: row-equivalent to `A` and in reduced echelon form. -/
def IsReducedEchelonFormOf {m n : Nat}
    (A B : Matrix (Fin m) (Fin n) R) : Prop :=
  RowEquivalent A B ∧ IsReducedEchelonForm (M := B)

lemma IsReducedEchelonFormOf.rowEquivalent {m n : Nat}
    {A B : Matrix (Fin m) (Fin n) R} (h : IsReducedEchelonFormOf (A := A) B) :
    RowEquivalent A B :=
  h.1

lemma IsReducedEchelonFormOf.reduced {m n : Nat}
    {A B : Matrix (Fin m) (Fin n) R} (h : IsReducedEchelonFormOf (A := A) B) :
    IsReducedEchelonForm (M := B) :=
  h.2

lemma isReducedEchelonFormOf_mk {m n : Nat}
    {A B : Matrix (Fin m) (Fin n) R}
    (hRow : RowEquivalent A B)
    (hRed : IsReducedEchelonForm (M := B)) :
    IsReducedEchelonFormOf (A := A) B :=
  ⟨hRow, hRed⟩

section Canonical

variable [DecidableEq R]

/-- Canonical-RREF witness: `B` is exactly the output of `rowReducedEchelonForm` on `A`. -/
def IsCanonicalRrefOf {m n : Nat}
    (A B : Matrix (Fin m) (Fin n) R) : Prop :=
  B = rowReducedEchelonForm A

lemma isCanonicalRrefOf_rowReducedEchelonForm {m n : Nat}
    (A : Matrix (Fin m) (Fin n) R) :
    IsCanonicalRrefOf A (rowReducedEchelonForm A) :=
  rfl

theorem IsCanonicalRrefOf.unique {m n : Nat}
    {A B B' : Matrix (Fin m) (Fin n) R}
    (hB : IsCanonicalRrefOf A B)
    (hB' : IsCanonicalRrefOf A B') :
    B = B' := by
  calc
    B = rowReducedEchelonForm A := hB
    _ = B' := hB'.symm

lemma IsCanonicalRrefOf.reduced {m n : Nat}
    {A B : Matrix (Fin m) (Fin n) R}
    (hB : IsCanonicalRrefOf A B) :
    IsReducedEchelonForm (M := B) := by
  subst hB
  simpa using rowReducedEchelonForm_isReducedEchelon (M := A)

end Canonical

/-- Row-equivalent matrices have the same homogeneous solution set. -/
lemma RowEquivalent.mul_eq_zero_iff {m n : Nat}
    {A B : Matrix (Fin m) (Fin n) R}
    (hAB : RowEquivalent A B)
    (x : Matrix (Fin n) (Fin 1) R) :
    A * x = 0 ↔ B * x = 0 := by
  rcases hAB with ⟨U, rfl⟩
  constructor
  · intro h
    simp [h, Matrix.mul_assoc]
  · intro h
    have hmul := congrArg (fun Y : Matrix (Fin m) (Fin 1) R =>
      ((↑(U⁻¹) : Matrix (Fin m) (Fin m) R) * Y)) h
    simpa [Matrix.mul_assoc] using hmul

/--
If `B` and `B'` come from the same source by row-equivalence,
they define the same homogeneous equations.
-/
lemma rowEquivalent_common_source_mul_eq_zero_iff {m n : Nat}
    {A B B' : Matrix (Fin m) (Fin n) R}
    (hAB : RowEquivalent A B)
    (hAB' : RowEquivalent A B')
    (x : Matrix (Fin n) (Fin 1) R) :
    B * x = 0 ↔ B' * x = 0 := by
  have hBB' : RowEquivalent B B' :=
    RowEquivalent.trans (RowEquivalent.symm hAB) hAB'
  simpa using (RowEquivalent.mul_eq_zero_iff (hAB := hBB') x)

/-- Semantic target for full RREF uniqueness (stage 2). -/
def RrefUniquenessSemanticGoal {m n : Nat}
    (A : Matrix (Fin m) (Fin n) R) : Prop :=
  ∀ {B B' : Matrix (Fin m) (Fin n) R},
    IsReducedEchelonFormOf A B →
    IsReducedEchelonFormOf A B' →
    B = B'

end Matrix
