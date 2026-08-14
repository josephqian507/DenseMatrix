/-
Copyright (c) 2026 Provable Computation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Provable Computation contributors
-/

import ProvableComputation.LinearAlgebra.DenseMatrix.GaussianElimination.Elementary
import ProvableComputation.LinearAlgebra.DenseMatrix.GaussianElimination.Rref

/-!
# Dense RREF semantics and uniqueness

This file proves that two reduced dense matrices row-equivalent to the same source are
equal. The proof works directly with dense entries and the native `leftMul` witness for
row equivalence.
-/

namespace DenseMatrix

variable {R : Type} [Field R]
variable {m n : Nat}

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

/-- Dense row-equivalent matrices have the same homogeneous solution set in Matrix view. -/
theorem RowEquivalent.mul_eq_zero_iff {A B : DenseMatrix m n R}
    (hAB : RowEquivalent A B)
    (x : Matrix (Fin n) (Fin 1) R) :
    A.toMatrix * x = 0 ↔ B.toMatrix * x = 0 := by
  rcases hAB with ⟨U, rfl⟩
  constructor
  · intro h
    simp [toMatrix_leftMul, Matrix.mul_assoc, h]
  · intro h
    have hmul := congrArg
      (fun Y : Matrix (Fin m) (Fin 1) R ↦
        ((↑(U⁻¹) : Matrix (Fin m) (Fin m) R) * Y)) h
    simpa [toMatrix_leftMul, Matrix.mul_assoc] using hmul

/--
Dense matrices row-equivalent to a common source have the same homogeneous
solution set in Matrix view.
-/
theorem rowEquivalent_common_source_mul_eq_zero_iff
    {A B B' : DenseMatrix m n R}
    (hAB : RowEquivalent A B)
    (hAB' : RowEquivalent A B')
    (x : Matrix (Fin n) (Fin 1) R) :
    B.toMatrix * x = 0 ↔ B'.toMatrix * x = 0 := by
  have hBB' : RowEquivalent B B' :=
    RowEquivalent.trans (RowEquivalent.symm hAB) hAB'
  exact RowEquivalent.mul_eq_zero_iff hBB' x

/--
In reduced form, every non-pivot row has `0` in a pivot column.

This combines "zero above pivot" and "zero below pivot" into one lemma by
splitting on the row order relation.
-/
private theorem reduced_pivot_col_zero_ne
    {M : DenseMatrix m n R}
    (hRed : IsReducedEchelonForm M)
    {i r : Fin m} {p : Fin n}
    (hp : IsPivot M i p)
    (hr : r ≠ i) :
    M.get r p = 0 := by
  by_cases hri : r < i
  · exact hRed.pivot_column_zero_above i r p hri hp
  · have hir_or_eq : i < r ∨ i = r := lt_or_eq_of_le (le_of_not_gt hri)
    cases hir_or_eq with
    | inl hir =>
        exact hRed.echelon.pivot_column_zero_below i r p hir hp
    | inr hir_eq =>
        exact (hr hir_eq.symm).elim

/--
Kronecker-delta view of a pivot column.

For a pivot `(i,p)` in reduced form, column `p` equals `1` at row `i` and `0`
everywhere else.
-/
private theorem reduced_pivot_col_unit
    {M : DenseMatrix m n R}
    (hRed : IsReducedEchelonForm M)
    {i r : Fin m} {p : Fin n}
    (hp : IsPivot M i p) :
    M.get r p = if r = i then 1 else 0 := by
  by_cases hri : r = i
  · subst hri
    simpa using hRed.pivot_is_one r p hp
  · simp [hri, reduced_pivot_col_zero_ne hRed hp hri]

/--
Coefficient extraction from a pivot column.

If `B = leftMul U C` and column `q` of `C` is a pivot column with pivot row
`k`, then entry `B[i,q]` is exactly the coefficient `U[i,k]`.
-/
private theorem coeff_from_pivot_column
    {B C : DenseMatrix m n R}
    (hC : IsReducedEchelonForm C)
    (U : Matrix (Fin m) (Fin m) R)
    (hBC : B = leftMul U C)
    {k i : Fin m} {q : Fin n}
    (hq : IsPivot C k q) :
    B.get i q = U i k := by
  rw [hBC, get_leftMul]
  calc
    (∑ t, U i t * C.get t q) =
        ∑ t, U i t * (if t = k then 1 else 0) := by
      refine Finset.sum_congr rfl ?_
      intro t _
      rw [reduced_pivot_col_unit hC hq]
    _ = U i k := by simp

/--
Row-level matching relation used in the uniqueness proof.

At row `i`, either both matrices are zero rows, or they share the same pivot
column at that row.
-/
private def RowMatch (B C : DenseMatrix m n R) (i : Fin m) : Prop :=
  (RowIsZero B i ∧ RowIsZero C i) ∨ ∃ p : Fin n, IsPivot B i p ∧ IsPivot C i p

/--
Pivot-column transfer lemma (from left matrix to right matrix).

Given row-equivalence and reducedness of `C`, every pivot column appearing in
`B` must also appear as a pivot column in `C` (possibly at another row).
-/
private theorem pivot_exists_in_right
    {B C : DenseMatrix m n R}
    (hBC : RowEquivalent B C)
    (hC : IsReducedEchelonForm C)
    {i : Fin m} {p : Fin n}
    (hpB : IsPivot B i p) :
    ∃ k : Fin m, IsPivot C k p := by
  rcases RowEquivalent.symm hBC with ⟨UUnit, hUraw⟩
  let U : Matrix (Fin m) (Fin m) R := (UUnit : Matrix (Fin m) (Fin m) R)
  have hU : B = leftMul U C := by simpa [U] using hUraw
  by_contra hnone
  have hsumZero : (∑ t, U i t * C.get t p) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro t _
    cases hCt : hC.echelon.row_zero_or_pivot t with
    | inl hZero =>
        simp [hZero p]
    | inr hPivot =>
        rcases hPivot with ⟨q, hq⟩
        by_cases hqp : q = p
        · exact (hnone ⟨t, by simpa [hqp] using hq⟩).elim
        · rcases lt_or_gt_of_ne hqp with hqLt | hpLt
          · have hUit : U i t = 0 := by
              have hCoeff : B.get i q = U i t :=
                coeff_from_pivot_column hC U hU hq
              have hBiq : B.get i q = 0 := hpB.2 q hqLt
              exact hCoeff.symm.trans hBiq
            simp [hUit]
          · have hCtp : C.get t p = 0 := hq.2 p hpLt
            simp [hCtp]
  have hBpZero : B.get i p = 0 := by
    rw [hU, get_leftMul]
    exact hsumZero
  exact hpB.1 hBpZero

/--
Symmetric pivot-column transfer lemma (right matrix to left matrix).

This is `pivot_exists_in_right` applied to the symmetric row-equivalence.
-/
private theorem pivot_exists_in_left
    {B C : DenseMatrix m n R}
    (hBC : RowEquivalent B C)
    (hB : IsReducedEchelonForm B)
    {i : Fin m} {p : Fin n}
    (hpC : IsPivot C i p) :
    ∃ k : Fin m, IsPivot B k p := by
  simpa using
    (pivot_exists_in_right (hBC := RowEquivalent.symm hBC) (hC := hB) hpC)

/--
Key row-by-row alignment theorem under row-equivalence and reducedness.

For each row index `i`, matrices `B` and `C` either are both zero rows or
share the same pivot column at row `i`.
-/
private theorem reduced_rowMatch_of_rowEquivalent
    {B C : DenseMatrix m n R}
    (hBC : RowEquivalent B C)
    (hB : IsReducedEchelonForm B)
    (hC : IsReducedEchelonForm C) :
    ∀ i : Fin m, RowMatch B C i := by
  have hMatchNat : ∀ iNat : Nat, ∀ hi : iNat < m, RowMatch B C ⟨iNat, hi⟩ := by
    intro iNat
    refine Nat.strong_induction_on iNat ?_
    intro iNat ih hi
    let iFin : Fin m := ⟨iNat, hi⟩
    cases hBi : hB.echelon.row_zero_or_pivot iFin with
    | inl hBZero =>
        have hCZero : RowIsZero C iFin := by
          cases hCi : hC.echelon.row_zero_or_pivot iFin with
          | inl hZero =>
              exact hZero
          | inr hPivot =>
              rcases hPivot with ⟨q, hqC⟩
              rcases pivot_exists_in_left (hBC := hBC) (hB := hB) hqC with ⟨k, hkB⟩
              rcases lt_trichotomy k.1 iNat with hkLt | hkEq | hiLt
              · have hkMatch : RowMatch B C k := ih k.1 hkLt k.2
                cases hkMatch with
                | inl hZeroPair =>
                    exact (RowIsZero.not_isPivot hZeroPair.1 hkB).elim
                | inr hPivotPair =>
                    rcases hPivotPair with ⟨qk, hkB', hkCk⟩
                    have hqk : qk = q := IsPivot.eq_of_left hkB' hkB
                    have hkCq : IsPivot C k q := by simpa [hqk] using hkCk
                    have hkLt' : k < iFin := by simpa [Fin.lt_def, iFin] using hkLt
                    have hqLtq : q < q :=
                      hC.echelon.pivots_strictly_increasing k iFin q q hkLt' hkCq hqC
                    exact (lt_irrefl _ hqLtq).elim
              · have hkEqFin : k = iFin := Fin.ext hkEq
                subst hkEqFin
                exact (RowIsZero.not_isPivot hBZero hkB).elim
              · have hiLt' : iFin < k := by simpa [Fin.lt_def, iFin] using hiLt
                have hkZero : RowIsZero B k :=
                  hB.echelon.zero_rows_bottom iFin k hiLt' hBZero
                exact (RowIsZero.not_isPivot hkZero hkB).elim
        exact Or.inl ⟨hBZero, hCZero⟩
    | inr hPivotB =>
        rcases hPivotB with ⟨p, hpB⟩
        have hCNonzero : ¬ RowIsZero C iFin := by
          intro hCZero
          rcases pivot_exists_in_right (hBC := hBC) (hC := hC) hpB with ⟨k, hkC⟩
          rcases lt_trichotomy k.1 iNat with hkLt | hkEq | hiLt
          · have hkMatch : RowMatch B C k := ih k.1 hkLt k.2
            cases hkMatch with
            | inl hZeroPair =>
                exact RowIsZero.not_isPivot hZeroPair.2 hkC
            | inr hPivotPair =>
                rcases hPivotPair with ⟨pk, hkB, hkC'⟩
                have hpk : pk = p := IsPivot.eq_of_left hkC' hkC
                have hkBp : IsPivot B k p := by simpa [hpk] using hkB
                have hkLt' : k < iFin := by simpa [Fin.lt_def, iFin] using hkLt
                have hpLtp : p < p :=
                  hB.echelon.pivots_strictly_increasing k iFin p p hkLt' hkBp hpB
                exact lt_irrefl _ hpLtp
          · have hkEqFin : k = iFin := Fin.ext hkEq
            subst hkEqFin
            exact RowIsZero.not_isPivot hCZero hkC
          · have hiLt' : iFin < k := by simpa [Fin.lt_def, iFin] using hiLt
            have hkZero : RowIsZero C k :=
              hC.echelon.zero_rows_bottom iFin k hiLt' hCZero
            exact RowIsZero.not_isPivot hkZero hkC
        have hCPivot : ∃ q : Fin n, IsPivot C iFin q := by
          cases hCi : hC.echelon.row_zero_or_pivot iFin with
          | inl hZero => exact (hCNonzero hZero).elim
          | inr hPivot => exact hPivot
        rcases hCPivot with ⟨q, hqC⟩
        have hpLeQ : p ≤ q := by
          by_contra hNotLe
          have hqLtP : q < p := lt_of_not_ge hNotLe
          rcases pivot_exists_in_left (hBC := hBC) (hB := hB) hqC with ⟨k, hkBq⟩
          rcases lt_trichotomy k.1 iNat with hkLt | hkEq | hiLt
          · have hkMatch : RowMatch B C k := ih k.1 hkLt k.2
            cases hkMatch with
            | inl hZeroPair =>
                exact (RowIsZero.not_isPivot hZeroPair.1 hkBq).elim
            | inr hPivotPair =>
                rcases hPivotPair with ⟨qk, hkB, hkCk⟩
                have hqk : qk = q := IsPivot.eq_of_left hkB hkBq
                have hkCq : IsPivot C k q := by simpa [hqk] using hkCk
                have hkLt' : k < iFin := by simpa [Fin.lt_def, iFin] using hkLt
                have hqLtq : q < q :=
                  hC.echelon.pivots_strictly_increasing k iFin q q hkLt' hkCq hqC
                exact (lt_irrefl _ hqLtq).elim
          · have hkEqFin : k = iFin := Fin.ext hkEq
            subst hkEqFin
            have hpEqQ : p = q := IsPivot.eq_of_left hpB hkBq
            exact (ne_of_lt hqLtP) hpEqQ.symm
          · have hiLt' : iFin < k := by simpa [Fin.lt_def, iFin] using hiLt
            have hpLtQ : p < q :=
              hB.echelon.pivots_strictly_increasing iFin k p q hiLt' hpB hkBq
            exact (lt_irrefl _ (hqLtP.trans hpLtQ)).elim
        have hqLeP : q ≤ p := by
          by_contra hNotLe
          have hpLtQ : p < q := lt_of_not_ge hNotLe
          rcases pivot_exists_in_right (hBC := hBC) (hC := hC) hpB with ⟨k, hkCp⟩
          rcases lt_trichotomy k.1 iNat with hkLt | hkEq | hiLt
          · have hkMatch : RowMatch B C k := ih k.1 hkLt k.2
            cases hkMatch with
            | inl hZeroPair =>
                exact (RowIsZero.not_isPivot hZeroPair.2 hkCp).elim
            | inr hPivotPair =>
                rcases hPivotPair with ⟨pk, hkBk, hkCk⟩
                have hpk : pk = p := IsPivot.eq_of_left hkCk hkCp
                have hkBp : IsPivot B k p := by simpa [hpk] using hkBk
                have hkLt' : k < iFin := by simpa [Fin.lt_def, iFin] using hkLt
                have hpLtp : p < p :=
                  hB.echelon.pivots_strictly_increasing k iFin p p hkLt' hkBp hpB
                exact (lt_irrefl _ hpLtp).elim
          · have hkEqFin : k = iFin := Fin.ext hkEq
            subst hkEqFin
            have hqEqP : q = p := IsPivot.eq_of_left hqC hkCp
            exact (ne_of_lt hpLtQ) hqEqP.symm
          · have hiLt' : iFin < k := by simpa [Fin.lt_def, iFin] using hiLt
            have hqLtP : q < p :=
              hC.echelon.pivots_strictly_increasing iFin k q p hiLt' hqC hkCp
            exact (lt_irrefl _ (hpLtQ.trans hqLtP)).elim
        have hpq : p = q := le_antisymm hpLeQ hqLeP
        exact Or.inr ⟨p, hpB, by simpa [hpq] using hqC⟩
  intro i
  simpa using hMatchNat i.1 i.2

/--
Semantic uniqueness under row-equivalence.

If `B` and `C` are reduced and row-equivalent, then they are entrywise equal.
-/
private theorem reduced_unique_of_rowEquivalent
    {B C : DenseMatrix m n R}
    (hBC : RowEquivalent B C)
    (hB : IsReducedEchelonForm B)
    (hC : IsReducedEchelonForm C) :
    B = C := by
  rcases RowEquivalent.symm hBC with ⟨UUnit, hUraw⟩
  let U : Matrix (Fin m) (Fin m) R := (UUnit : Matrix (Fin m) (Fin m) R)
  have hU : B = leftMul U C := by simpa [U] using hUraw
  have hMatch : ∀ i : Fin m, RowMatch B C i :=
    reduced_rowMatch_of_rowEquivalent hBC hB hC
  ext i j
  calc
    B.get i j = ∑ t, U i t * C.get t j := by rw [hU, get_leftMul]
    _ = ∑ t, (if i = t then 1 else 0) * C.get t j := by
      refine Finset.sum_congr rfl ?_
      intro t _
      cases hMatch t with
      | inl hZeroPair =>
          simp [hZeroPair.2 j]
      | inr hPivotPair =>
          rcases hPivotPair with ⟨p, hpBt, hpCt⟩
          have hCoeff : U i t = B.get i p :=
            (coeff_from_pivot_column hC U hU hpCt).symm
          have hUnit : B.get i p = if i = t then 1 else 0 :=
            reduced_pivot_col_unit hB hpBt
          rw [hCoeff, hUnit]
    _ = C.get i j := by simp

/-- Any two dense reduced-echelon representatives of one source are equal. -/
theorem IsReducedEchelonFormOf.unique {A B B' : DenseMatrix m n R}
    (hB : IsReducedEchelonFormOf A B)
    (hB' : IsReducedEchelonFormOf A B') : B = B' := by
  classical
  have hBB' : RowEquivalent B B' :=
    RowEquivalent.trans (RowEquivalent.symm hB.rowEquivalent) hB'.rowEquivalent
  exact reduced_unique_of_rowEquivalent hBB' hB.reduced hB'.reduced

/-- Semantic stage-2 specification of dense RREF uniqueness. -/
def RrefUniquenessSemanticGoal (A : DenseMatrix m n R) : Prop :=
  ∀ {B B' : DenseMatrix m n R},
    IsReducedEchelonFormOf A B →
    IsReducedEchelonFormOf A B' →
    B = B'

/-- The semantic stage-2 specification holds for dense matrices. -/
theorem rrefUniquenessSemanticGoal_holds (A : DenseMatrix m n R) :
    RrefUniquenessSemanticGoal A := fun {_ _} hB hB' ↦ hB.unique hB'

section Canonical

variable [DecidableEq R]

/-- A dense matrix is the canonical RREF of `A` when it is the computed output. -/
def IsCanonicalRrefOf (A B : DenseMatrix m n R) : Prop :=
  B = (DenseMatrix.reducedRowEchelonForm A).matrix

/-- The computed dense RREF is canonical for its input. -/
theorem isCanonicalRrefOf_reducedRowEchelonForm (A : DenseMatrix m n R) :
    IsCanonicalRrefOf A (DenseMatrix.reducedRowEchelonForm A).matrix :=
  rfl

/-- Alias matching the computed-output naming used by the Matrix API. -/
theorem reducedRowEchelonForm_isCanonicalRrefOf (A : DenseMatrix m n R) :
    IsCanonicalRrefOf A (DenseMatrix.reducedRowEchelonForm A).matrix :=
  isCanonicalRrefOf_reducedRowEchelonForm A

/-- Canonical dense RREF representatives are unique by definition. -/
theorem IsCanonicalRrefOf.unique {A B B' : DenseMatrix m n R}
    (hB : IsCanonicalRrefOf A B) (hB' : IsCanonicalRrefOf A B') : B = B' :=
  hB.trans hB'.symm

end Canonical

end DenseMatrix
