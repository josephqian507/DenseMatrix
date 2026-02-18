import ProvableComputation.linear_algebra.RowEquivalent
import ProvableComputation.linear_algebra.IsInReducedEchelonFormProofs

namespace Matrix

variable {R : Type} [Field R]

/-- `B` is an RREF representative of `A`: row-equivalent to `A` and in reduced echelon form. -/
def IsReducedEchelonFormOf {m n : Nat}
    [DecidableEq R]
    (A B : Matrix (Fin m) (Fin n) R) : Prop :=
  RowEquivalent A B ∧ IsReducedEchelonForm (M := B)

lemma IsReducedEchelonFormOf.rowEquivalent {m n : Nat}
    [DecidableEq R]
    {A B : Matrix (Fin m) (Fin n) R} (h : IsReducedEchelonFormOf (A := A) B) :
    RowEquivalent A B :=
  h.1

lemma IsReducedEchelonFormOf.reduced {m n : Nat}
    [DecidableEq R]
    {A B : Matrix (Fin m) (Fin n) R} (h : IsReducedEchelonFormOf (A := A) B) :
    IsReducedEchelonForm (M := B) :=
  h.2

lemma isReducedEchelonFormOf_mk {m n : Nat}
    [DecidableEq R]
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
  B = (rowReducedEchelonForm A).1

lemma isCanonicalRrefOf_rowReducedEchelonForm {m n : Nat}
    (A : Matrix (Fin m) (Fin n) R) :
    IsCanonicalRrefOf A (rowReducedEchelonForm A).1 :=
  rfl

theorem IsCanonicalRrefOf.unique {m n : Nat}
    {A B B' : Matrix (Fin m) (Fin n) R}
    (hB : IsCanonicalRrefOf A B)
    (hB' : IsCanonicalRrefOf A B') :
    B = B' := by
  calc
    B = (rowReducedEchelonForm A).1 := hB
    _ = B' := hB'.symm

lemma IsCanonicalRrefOf.reduced {m n : Nat}
    {A B : Matrix (Fin m) (Fin n) R}
    (hB : IsCanonicalRrefOf A B) :
    IsReducedEchelonForm (M := B) := by
  rcases hB with rfl
  simpa using rowReducedEchelonForm_isReducedEchelon (M := A)

end Canonical

section AlgorithmBridge

variable [DecidableEq R]

private theorem eliminateColGo_rowEquivalent
    {m n : Nat}
    (pivotRow : Fin m) (pivotCol : Fin n) (row : Nat)
    (cur : Matrix (Fin m) (Fin n) R) (steps : List (RowOp m R)) :
    RowEquivalent cur (eliminateCol.go pivotRow pivotCol row cur steps).1 := by
  rw [eliminateCol.go]
  split_ifs with hr
  · let i : Fin m := ⟨row, hr⟩
    by_cases hEq : i = pivotRow
    · simpa [i, hEq] using
        (eliminateColGo_rowEquivalent pivotRow pivotCol (row + 1) cur steps)
    · by_cases hcoeff : cur i pivotCol ≠ 0
      · let cur' := replace cur pivotRow i (-cur i pivotCol)
        let steps' := List.concat steps (.replace pivotRow i (-cur i pivotCol))
        have hreplace : RowEquivalent cur cur' := by
          dsimp [cur']
          exact rowEquivalent_replace
            (A := cur) (use := pivotRow) (toReplace := i) (k := -cur i pivotCol)
            (huse := by simpa [eq_comm] using hEq)
        have hrec : RowEquivalent cur' (eliminateCol.go pivotRow pivotCol (row + 1) cur' steps').1 := by
          simpa [cur', steps'] using
            (eliminateColGo_rowEquivalent pivotRow pivotCol (row + 1) cur' steps')
        simpa [i, hEq, hcoeff, cur', steps'] using RowEquivalent.trans hreplace hrec
      · simpa [i, hEq, hcoeff] using
          (eliminateColGo_rowEquivalent pivotRow pivotCol (row + 1) cur steps)
  · simpa using (RowEquivalent.refl cur)
termination_by m - row
decreasing_by
  · omega
  · omega
  · omega

private theorem eliminateCol_rowEquivalent
    {m n : Nat}
    (M : Matrix (Fin m) (Fin n) R) (pivotRow : Fin m) (pivotCol : Fin n)
    (steps : List (RowOp m R)) (reduced : Bool) :
    RowEquivalent M (eliminateCol M pivotRow pivotCol steps reduced).1 := by
  rw [eliminateCol]
  by_cases hred : reduced
  · simpa [hred] using
      (eliminateColGo_rowEquivalent (pivotRow := pivotRow) (pivotCol := pivotCol)
        (row := 0) (cur := M) (steps := steps))
  · simpa [hred] using
      (eliminateColGo_rowEquivalent (pivotRow := pivotRow) (pivotCol := pivotCol)
        (row := pivotRow.1) (cur := M) (steps := steps))

private theorem rrefAux_rowEquivalent
    {m n : Nat}
    (M : Matrix (Fin m) (Fin n) R) (row col : Nat)
    (steps : List (RowOp m R)) (reduced : Bool) :
    RowEquivalent M (rrefAux M row col steps reduced).1 := by
  rw [rrefAux.eq_1]
  split_ifs with hrow hcol
  · cases hcp : checkPivot M row col with
    | none =>
        simp only
        exact RowEquivalent.refl M
    | some prpc =>
        rcases prpc with ⟨pivotRow, pivotCol⟩
        let rowFin : Fin m := ⟨row, hrow⟩
        let m1 : Matrix (Fin m) (Fin n) R :=
          if pivotRow.1 = row then M else swapRow M rowFin pivotRow
        let steps1 : List (RowOp m R) := List.concat steps (.swap rowFin pivotRow)
        let pivotVal : R := m1 rowFin pivotCol
        let m2 : Matrix (Fin m) (Fin n) R :=
          if pivotVal = 1 then m1 else factor m1 rowFin pivotVal⁻¹
        let steps2 : List (RowOp m R) := List.concat steps1 (.factor rowFin pivotVal⁻¹)
        have hM1 : RowEquivalent M m1 := by
          by_cases hp : pivotRow.1 = row
          · simpa [m1, hp] using (RowEquivalent.refl M)
          · simpa [m1, hp] using (rowEquivalent_swapRow (A := M) rowFin pivotRow)
        have hpivot_ne_zero : pivotVal ≠ 0 := by
          have hnon : M pivotRow pivotCol ≠ 0 :=
            checkPivot_some_nonzero (M := M) row col (h := by simp [hcp])
          by_cases hp : pivotRow.1 = row
          · have hroweq : rowFin = pivotRow := by
              exact Fin.ext (by simpa [rowFin] using hp.symm)
            subst hroweq
            simpa [m1, hp, pivotVal] using hnon
          · have hrowne : rowFin ≠ pivotRow := by
              intro hEq
              exact hp (by simpa [rowFin] using (congrArg Fin.val hEq).symm)
            have hpres :
                (swapRow M rowFin pivotRow) rowFin pivotCol = M pivotRow pivotCol := by
              simp [swapRow, of_apply, hrowne]
            simpa [m1, hp, pivotVal, hpres] using hnon
        have hM2 : RowEquivalent m1 m2 := by
          by_cases hv : pivotVal = 1
          · simpa [m2, hv] using (RowEquivalent.refl m1)
          · have hfac : RowEquivalent m1 (factor m1 rowFin pivotVal⁻¹) :=
              rowEquivalent_factor (A := m1) (i := rowFin) (j := pivotVal⁻¹)
                (hj := inv_ne_zero hpivot_ne_zero)
            simpa [m2, hv] using hfac
        cases hp : eliminateCol m2 rowFin pivotCol steps2 reduced with
        | mk m3 steps3 =>
            have hM3raw : RowEquivalent m2 (eliminateCol m2 rowFin pivotCol steps2 reduced).1 := by
              simpa using
                (eliminateCol_rowEquivalent (M := m2) (pivotRow := rowFin) (pivotCol := pivotCol)
                  (steps := steps2) (reduced := reduced))
            have hRec : RowEquivalent m3 (rrefAux m3 (row + 1) (col + 1) steps3 reduced).1 := by
              simpa using
                (rrefAux_rowEquivalent (M := m3) (row := row + 1) (col := col + 1)
                  (steps := steps3) (reduced := reduced))
            have hRecraw :
                RowEquivalent (eliminateCol m2 rowFin pivotCol steps2 reduced).1
                  (rrefAux
                    (eliminateCol m2 rowFin pivotCol steps2 reduced).1
                    (row + 1) (col + 1)
                    (eliminateCol m2 rowFin pivotCol steps2 reduced).2 reduced).1 := by
              simpa [hp] using hRec
            simpa [m1, m2, steps1, steps2, pivotVal, rowFin, hcp, hp, List.concat_eq_append] using
              RowEquivalent.trans (RowEquivalent.trans hM1 (RowEquivalent.trans hM2 hM3raw)) hRecraw
  · simp only
    exact RowEquivalent.refl M
  · simp only
    exact RowEquivalent.refl M
termination_by m - row
decreasing_by
  · omega

theorem rowReducedEchelonForm_rowEquivalent
    {m n : Nat}
    (A : Matrix (Fin m) (Fin n) R) :
    RowEquivalent A (rowReducedEchelonForm A).1 := by
  simpa [rowReducedEchelonForm] using
    (rrefAux_rowEquivalent (M := A) (row := 0) (col := 0) (steps := List.nil) (reduced := true))

theorem rowReducedEchelonForm_isReducedEchelonFormOf
    {m n : Nat}
    (A : Matrix (Fin m) (Fin n) R) :
    IsReducedEchelonFormOf A (rowReducedEchelonForm A).1 := by
  refine ⟨rowReducedEchelonForm_rowEquivalent (A := A), ?_⟩
  simpa using rowReducedEchelonForm_isReducedEchelon (M := A)

theorem rowReducedEchelonForm_isEchelonFormOf
    {m n : Nat}
    (A : Matrix (Fin m) (Fin n) R) :
    IsEchelonFormOf (A := A) ((rowReducedEchelonForm A).1) := by
  refine ⟨rowReducedEchelonForm_rowEquivalent (A := A), ?_⟩
  exact (rowReducedEchelonForm_isReducedEchelon (M := A)).echelon

lemma rowReducedEchelonForm_isCanonicalRrefOf
    {m n : Nat}
    (A : Matrix (Fin m) (Fin n) R) :
    IsCanonicalRrefOf A (rowReducedEchelonForm A).1 :=
  rfl

end AlgorithmBridge

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

private lemma reduced_pivot_col_zero_ne {m n : Nat}
    {M : Matrix (Fin m) (Fin n) R}
    (hRed : IsReducedEchelonForm (M := M))
    {i r : Fin m} {p : Fin n}
    (hp : IsPivot M i p)
    (hr : r ≠ i) :
    M r p = 0 := by
  by_cases hri : r < i
  · exact hRed.pivot_column_zero_above i r p hri hp
  · have hir_or_eq : i < r ∨ i = r := lt_or_eq_of_le (le_of_not_gt hri)
    cases hir_or_eq with
    | inl hir =>
        exact hRed.echelon.pivot_column_zero_below i r p hir hp
    | inr hir_eq =>
        exact (hr hir_eq.symm).elim

private lemma reduced_pivot_col_unit {m n : Nat}
    {M : Matrix (Fin m) (Fin n) R}
    (hRed : IsReducedEchelonForm (M := M))
    {i r : Fin m} {p : Fin n}
    (hp : IsPivot M i p) :
    M r p = if r = i then 1 else 0 := by
  by_cases hri : r = i
  · subst hri
    simpa using hRed.pivot_is_one r p hp
  · simp [hri, reduced_pivot_col_zero_ne hRed hp hri]

private lemma coeff_from_pivot_column {m n : Nat}
    {B C : Matrix (Fin m) (Fin n) R}
    (hC : IsReducedEchelonForm (M := C))
    (U : Matrix (Fin m) (Fin m) R)
    (hBC : B = U * C)
    {k i : Fin m} {q : Fin n}
    (hq : IsPivot C k q) :
    B i q = U i k := by
  have hEntry : B i q = (U * C) i q := by simp [hBC]
  rw [Matrix.mul_apply] at hEntry
  have hsum : (∑ t, U i t * C t q) = U i k := by
    calc
      (∑ t, U i t * C t q)
          = ∑ t, U i t * (if t = k then 1 else 0) := by
              refine Finset.sum_congr rfl ?_
              intro t _
              simp [reduced_pivot_col_unit hC hq]
      _ = U i k := by simp
  simpa [hsum] using hEntry

private def RowMatch {m n : Nat}
    (B C : Matrix (Fin m) (Fin n) R) (i : Fin m) : Prop :=
  (RowIsZero B i ∧ RowIsZero C i) ∨ ∃ p : Fin n, IsPivot B i p ∧ IsPivot C i p

private lemma pivot_exists_in_right {m n : Nat}
    {B C : Matrix (Fin m) (Fin n) R}
    (hBC : RowEquivalent B C)
    (hC : IsReducedEchelonForm (M := C))
    {i : Fin m} {p : Fin n}
    (hpB : IsPivot B i p) :
    ∃ k : Fin m, IsPivot C k p := by
  rcases RowEquivalent.symm hBC with ⟨UUnit, hUraw⟩
  let U : Matrix (Fin m) (Fin m) R := (UUnit : Matrix (Fin m) (Fin m) R)
  have hU : B = U * C := by simpa [U] using hUraw
  by_contra hnone
  have hsumZero : (∑ t, U i t * C t p) = 0 := by
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
              have hCoeff : B i q = U i t :=
                coeff_from_pivot_column (hC := hC) (U := U) (hBC := hU)
                  (k := t) (i := i) (q := q) hq
              have hBiq : B i q = 0 := hpB.2 q hqLt
              calc
                U i t = B i q := hCoeff.symm
                _ = 0 := hBiq
            simp [hUit]
          · have hCtp : C t p = 0 := hq.2 p hpLt
            simp [hCtp]
  have hBpZero : B i p = 0 := by
    calc
      B i p = (U * C) i p := by simp [hU]
      _ = ∑ t, U i t * C t p := by simp [Matrix.mul_apply]
      _ = 0 := hsumZero
  exact hpB.1 hBpZero

private lemma pivot_exists_in_left {m n : Nat}
    {B C : Matrix (Fin m) (Fin n) R}
    (hBC : RowEquivalent B C)
    (hB : IsReducedEchelonForm (M := B))
    {i : Fin m} {p : Fin n}
    (hpC : IsPivot C i p) :
    ∃ k : Fin m, IsPivot B k p := by
  simpa using
    (pivot_exists_in_right (hBC := RowEquivalent.symm hBC) (hC := hB) hpC)

private theorem reduced_rowMatch_of_rowEquivalent {m n : Nat}
    {B C : Matrix (Fin m) (Fin n) R}
    (hBC : RowEquivalent B C)
    (hB : IsReducedEchelonForm (M := B))
    (hC : IsReducedEchelonForm (M := C)) :
    ∀ i : Fin m, RowMatch (R := R) B C i := by
  have hMatchNat : ∀ iNat : Nat, ∀ hi : iNat < m, RowMatch (R := R) B C ⟨iNat, hi⟩ := by
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
              · have hkMatch : RowMatch (R := R) B C k := ih k.1 hkLt k.2
                cases hkMatch with
                | inl hZeroPair =>
                    exact (RowIsZero.not_isPivot (hzero := hZeroPair.1) (hp := hkB)).elim
                | inr hPivotPair =>
                    rcases hPivotPair with ⟨qk, hkB', hkCk⟩
                    have hqk : qk = q := IsPivot.eq_of_left hkB' hkB
                    have hkCq : IsPivot C k q := by simpa [hqk] using hkCk
                    have hkLt' : k < iFin := by simpa [iFin] using hkLt
                    have hqLtq : q < q :=
                      hC.echelon.pivots_strictly_increasing k iFin q q hkLt' hkCq hqC
                    exact (lt_irrefl _ hqLtq).elim
              · have hkEqFin : k = iFin := Fin.ext hkEq
                subst hkEqFin
                exact (RowIsZero.not_isPivot (hzero := hBZero) (hp := hkB)).elim
              · have hiLt' : iFin < k := by simpa [iFin] using hiLt
                have hkZero : RowIsZero B k :=
                  hB.echelon.zero_rows_bottom iFin k hiLt' hBZero
                exact (RowIsZero.not_isPivot (hzero := hkZero) (hp := hkB)).elim
        exact Or.inl ⟨hBZero, hCZero⟩
    | inr hPivotB =>
        rcases hPivotB with ⟨p, hpB⟩
        have hCNonzero : ¬ RowIsZero C iFin := by
          intro hCZero
          rcases pivot_exists_in_right (hBC := hBC) (hC := hC) hpB with ⟨k, hkC⟩
          rcases lt_trichotomy k.1 iNat with hkLt | hkEq | hiLt
          · have hkMatch : RowMatch (R := R) B C k := ih k.1 hkLt k.2
            cases hkMatch with
            | inl hZeroPair =>
                exact (RowIsZero.not_isPivot (hzero := hZeroPair.2) (hp := hkC)).elim
            | inr hPivotPair =>
                rcases hPivotPair with ⟨pk, hkB, hkC'⟩
                have hpk : pk = p := IsPivot.eq_of_left hkC' hkC
                have hkBp : IsPivot B k p := by simpa [hpk] using hkB
                have hkLt' : k < iFin := by simpa [iFin] using hkLt
                have hpLtp : p < p :=
                  hB.echelon.pivots_strictly_increasing k iFin p p hkLt' hkBp hpB
                exact (lt_irrefl _ hpLtp).elim
          · have hkEqFin : k = iFin := Fin.ext hkEq
            subst hkEqFin
            exact (RowIsZero.not_isPivot (hzero := hCZero) (hp := hkC)).elim
          · have hiLt' : iFin < k := by simpa [iFin] using hiLt
            have hkZero : RowIsZero C k :=
              hC.echelon.zero_rows_bottom iFin k hiLt' hCZero
            exact (RowIsZero.not_isPivot (hzero := hkZero) (hp := hkC)).elim
        have hCPivot : ∃ q : Fin n, IsPivot C iFin q := by
          cases hCi : hC.echelon.row_zero_or_pivot iFin with
          | inl hZero =>
              exact (hCNonzero hZero).elim
          | inr hPivot =>
              exact hPivot
        rcases hCPivot with ⟨q, hqC⟩
        have hpLeQ : p ≤ q := by
          by_contra hNotLe
          have hqLtP : q < p := lt_of_not_ge hNotLe
          rcases pivot_exists_in_left (hBC := hBC) (hB := hB) hqC with ⟨k, hkBq⟩
          rcases lt_trichotomy k.1 iNat with hkLt | hkEq | hiLt
          · have hkMatch : RowMatch (R := R) B C k := ih k.1 hkLt k.2
            cases hkMatch with
            | inl hZeroPair =>
                exact (RowIsZero.not_isPivot (hzero := hZeroPair.1) (hp := hkBq)).elim
            | inr hPivotPair =>
                rcases hPivotPair with ⟨qk, hkB, hkCk⟩
                have hqk : qk = q := IsPivot.eq_of_left hkB hkBq
                have hkCq : IsPivot C k q := by simpa [hqk] using hkCk
                have hkLt' : k < iFin := by simpa [iFin] using hkLt
                have hqLtq : q < q :=
                  hC.echelon.pivots_strictly_increasing k iFin q q hkLt' hkCq hqC
                exact (lt_irrefl _ hqLtq).elim
          · have hkEqFin : k = iFin := Fin.ext hkEq
            subst hkEqFin
            have hpEqQ : p = q := IsPivot.eq_of_left hpB hkBq
            exact (ne_of_lt hqLtP) hpEqQ.symm
          · have hiLt' : iFin < k := by simpa [iFin] using hiLt
            have hpLtQ : p < q :=
              hB.echelon.pivots_strictly_increasing iFin k p q hiLt' hpB hkBq
            exact (lt_irrefl _ (hqLtP.trans hpLtQ)).elim
        have hqLeP : q ≤ p := by
          by_contra hNotLe
          have hpLtQ : p < q := lt_of_not_ge hNotLe
          rcases pivot_exists_in_right (hBC := hBC) (hC := hC) hpB with ⟨k, hkCp⟩
          rcases lt_trichotomy k.1 iNat with hkLt | hkEq | hiLt
          · have hkMatch : RowMatch (R := R) B C k := ih k.1 hkLt k.2
            cases hkMatch with
            | inl hZeroPair =>
                exact (RowIsZero.not_isPivot (hzero := hZeroPair.2) (hp := hkCp)).elim
            | inr hPivotPair =>
                rcases hPivotPair with ⟨pk, hkBk, hkCk⟩
                have hpk : pk = p := IsPivot.eq_of_left hkCk hkCp
                have hkBp : IsPivot B k p := by simpa [hpk] using hkBk
                have hkLt' : k < iFin := by simpa [iFin] using hkLt
                have hpLtp : p < p :=
                  hB.echelon.pivots_strictly_increasing k iFin p p hkLt' hkBp hpB
                exact (lt_irrefl _ hpLtp).elim
          · have hkEqFin : k = iFin := Fin.ext hkEq
            subst hkEqFin
            have hqEqP : q = p := IsPivot.eq_of_left hqC hkCp
            exact (ne_of_lt hpLtQ) hqEqP.symm
          · have hiLt' : iFin < k := by simpa [iFin] using hiLt
            have hqLtP : q < p :=
              hC.echelon.pivots_strictly_increasing iFin k q p hiLt' hqC hkCp
            exact (lt_irrefl _ (hpLtQ.trans hqLtP)).elim
        have hpq : p = q := le_antisymm hpLeQ hqLeP
        exact Or.inr ⟨p, hpB, by simpa [hpq] using hqC⟩
  intro i
  simpa using hMatchNat i.1 i.2

private theorem reduced_unique_of_rowEquivalent {m n : Nat}
    {B C : Matrix (Fin m) (Fin n) R}
    (hBC : RowEquivalent B C)
    (hB : IsReducedEchelonForm (M := B))
    (hC : IsReducedEchelonForm (M := C)) :
    B = C := by
  rcases RowEquivalent.symm hBC with ⟨UUnit, hUraw⟩
  let U : Matrix (Fin m) (Fin m) R := (UUnit : Matrix (Fin m) (Fin m) R)
  have hU : B = U * C := by simpa [U] using hUraw
  have hMatch : ∀ i : Fin m, RowMatch (R := R) B C i :=
    reduced_rowMatch_of_rowEquivalent (hBC := hBC) (hB := hB) (hC := hC)
  ext i j
  calc
    B i j = ∑ t, U i t * C t j := by
      calc
        B i j = (U * C) i j := by simp [hU]
        _ = ∑ t, U i t * C t j := by simp [Matrix.mul_apply]
    _ = ∑ t, (if i = t then 1 else 0) * C t j := by
      refine Finset.sum_congr rfl ?_
      intro t _
      cases hMatch t with
      | inl hZeroPair =>
          simp [hZeroPair.2 j]
      | inr hPivotPair =>
          rcases hPivotPair with ⟨p, hpBt, hpCt⟩
          have hCoeff : U i t = B i p :=
            (coeff_from_pivot_column (hC := hC) (U := U) (hBC := hU)
              (k := t) (i := i) (q := p) hpCt).symm
          have hUnit : B i p = if i = t then 1 else 0 :=
            reduced_pivot_col_unit hB hpBt
          simp [hCoeff, hUnit]
    _ = C i j := by simp

theorem IsReducedEchelonFormOf.unique {m n : Nat}
    [DecidableEq R]
    {A B B' : Matrix (Fin m) (Fin n) R}
    (hB : IsReducedEchelonFormOf A B)
    (hB' : IsReducedEchelonFormOf A B') :
    B = B' := by
  have hBB' : RowEquivalent B B' :=
    RowEquivalent.trans (RowEquivalent.symm hB.rowEquivalent) hB'.rowEquivalent
  exact reduced_unique_of_rowEquivalent (hBC := hBB') (hB := hB.reduced) (hC := hB'.reduced)

lemma IsReducedEchelonFormOf.canonical {m n : Nat}
    [DecidableEq R]
    {A B : Matrix (Fin m) (Fin n) R} (h : IsReducedEchelonFormOf (A := A) B) :
    B = (rowReducedEchelonForm A).1 := by
  exact IsReducedEchelonFormOf.unique h (rowReducedEchelonForm_isReducedEchelonFormOf (A := A))

/-- Semantic target for full RREF uniqueness (stage 2). -/
def RrefUniquenessSemanticGoal {m n : Nat}
    [DecidableEq R]
    (A : Matrix (Fin m) (Fin n) R) : Prop :=
  ∀ {B B' : Matrix (Fin m) (Fin n) R},
    IsReducedEchelonFormOf A B →
    IsReducedEchelonFormOf A B' →
    B = B'

theorem rrefUniquenessSemanticGoal_holds {m n : Nat}
    [DecidableEq R]
    (A : Matrix (Fin m) (Fin n) R) :
    RrefUniquenessSemanticGoal (A := A) := by
  intro B B' hB hB'
  exact IsReducedEchelonFormOf.unique hB hB'

end Matrix
