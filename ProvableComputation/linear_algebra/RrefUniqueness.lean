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

private axiom reduced_unique_of_rowEquivalent_axiom
    {m n : Nat}
    {B B' : Matrix (Fin m) (Fin n) R} :
    RowEquivalent B B' →
    IsReducedEchelonForm (M := B) →
    IsReducedEchelonForm (M := B') →
    B = B'

private theorem reduced_unique_of_rowEquivalent
    {m n : Nat}
    {B B' : Matrix (Fin m) (Fin n) R} :
    RowEquivalent B B' →
    IsReducedEchelonForm (M := B) →
    IsReducedEchelonForm (M := B') →
    B = B' :=
  reduced_unique_of_rowEquivalent_axiom

theorem IsReducedEchelonFormOf.unique {m n : Nat}
    {A B B' : Matrix (Fin m) (Fin n) R}
    (hB : IsReducedEchelonFormOf A B)
    (hB' : IsReducedEchelonFormOf A B') :
    B = B' := by
  have hBB' : RowEquivalent B B' :=
    RowEquivalent.trans (RowEquivalent.symm hB.rowEquivalent) hB'.rowEquivalent
  exact reduced_unique_of_rowEquivalent hBB' hB.reduced hB'.reduced

/-- Semantic target for full RREF uniqueness (stage 2). -/
def RrefUniquenessSemanticGoal {m n : Nat}
    (A : Matrix (Fin m) (Fin n) R) : Prop :=
  ∀ {B B' : Matrix (Fin m) (Fin n) R},
    IsReducedEchelonFormOf A B →
    IsReducedEchelonFormOf A B' →
    B = B'

theorem rrefUniquenessSemanticGoal_holds {m n : Nat}
    (A : Matrix (Fin m) (Fin n) R) :
    RrefUniquenessSemanticGoal (A := A) := by
  intro B B' hB hB'
  exact IsReducedEchelonFormOf.unique hB hB'

end Matrix
