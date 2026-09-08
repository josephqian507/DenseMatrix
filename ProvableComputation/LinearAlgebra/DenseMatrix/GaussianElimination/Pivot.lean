/-
Copyright (c) 2026 Joseph Qian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Qian, Junye Ji, Dhruv Bhatia
-/
import ProvableComputation.LinearAlgebra.DenseMatrix.GaussianElimination.Rref

/-!
# Shared proof lemmas for echelon / RREF routines

This file collects structural lemmas used by proofs around `checkPivot`,
`replace`, and `eliminateCol`.
The focus is to expose stable invariants of the executable procedures in
`Rref.lean` as reusable theorem statements.
-/

open DenseMatrix.GaussianEliminationInternal Matrix

namespace DenseMatrix

variable {α : Type} [Field α] [DecidableEq α]
variable {m n : ℕ}

set_option linter.style.longLine false

/-- Matrix output of `eliminateCol` when computing reduced row echelon form. -/
abbrev eliminateColM
    (M : DenseMatrix m n α) (pivotRow : Fin m) (pivotCol : Fin n) :
    DenseMatrix m n α :=
  (eliminateCol M pivotRow pivotCol List.nil true).1

/-- Matrix output of `eliminateColLoop` at any iteration of the loop. -/
abbrev eliminateColLoopMatrix
    (pivotRow : Fin m) (pivotCol : Fin n) (r : Nat)
    (cur : DenseMatrix m n α) (steps : List (DenseMatrix.RowOp m α)) :
    DenseMatrix m n α :=
  (eliminateColLoop pivotRow pivotCol r cur steps).1

private lemma eliminateColLoopAux_matrix_eq
    (pivotRow : Fin m) (pivotCol : Fin n) (pivotVal : α) (r : Nat)
    (cur : DenseMatrix m n α) (steps : List (DenseMatrix.RowOp m α))
    (hpivot : cur.get pivotRow pivotCol = pivotVal) :
    (eliminateColLoopAux pivotRow pivotCol pivotVal r cur steps).1 =
      eliminateColLoopMatrix pivotRow pivotCol r cur steps := by
  simp [eliminateColLoopMatrix, eliminateColLoop, hpivot]

/-! ## `checkPivot` search invariants -/

/--
If scanning column `col` from row `row` returns `none`, then every entry in
that column at rows `≥ row` is zero.
-/
private lemma scanRow_none_col_zero
    (M : DenseMatrix m n α) (col row : Nat) (hcol : col < n)
    (h : checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) row = none) :
    ∀ r : Fin m, row ≤ r.val → M.get r ⟨col, hcol⟩ = 0 := by
  classical
  have hrec :
      ∀ k row, m - row = k →
        checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) row = none →
        ∀ r : Fin m, row ≤ r.val → M.get r ⟨col, hcol⟩ = 0 := by
    intro k
    induction k with
    | zero =>
      intro row hk h r hr
      have hrow : m ≤ row := Nat.le_of_sub_eq_zero hk
      have : r.val < row := lt_of_lt_of_le r.isLt hrow
      exact (False.elim ((Nat.not_lt_of_ge hr) this))
    | succ k ih =>
      intro row hk h r hr
      have hrow : row < m := by omega
      rw [checkPivot.scanCol.scanRow, dif_pos hrow] at h
      by_cases hzero : M.get ⟨row, hrow⟩ ⟨col, hcol⟩ ≠ 0
      · simp [hzero] at h
      · have hnext : checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) (row + 1) = none := by
          simp only [hzero] at h
          exact h
        have hk' : m - (row + 1) = k :=
          by omega
        by_cases hreq : r.val = row
        · have hr' : r = ⟨row, hrow⟩ := by
            ext
            simp [hreq]
          subst hr'
          -- At the hit row, zero follows from the negated nonzero branch.
          have hzero' : M.get ⟨row, hrow⟩ ⟨col, hcol⟩ = 0 := by
            by_contra hne
            exact hzero hne
          exact hzero'
        · have hrlt : row < r.val := lt_of_le_of_ne hr (Ne.symm hreq)
          have hr' : row + 1 ≤ r.val := Nat.succ_le_of_lt hrlt
          exact ih (row + 1) hk' hnext r hr'
  exact hrec (m - row) row rfl h

/--
If no pivots are found when scanning from row `row` and column `col`, then all entries in the
submatrix with rows `≥ row` and columns `≥ col` are zero.
-/
lemma checkPivot_none_zero
    (M : DenseMatrix m n α) (row col : Nat)
    (h : checkPivot M row col = none) :
    ∀ j : Fin n, col ≤ j.val → ∀ r : Fin m, row ≤ r.val → M.get r j = 0 := by
  classical
  have hrec :
      ∀ k row col, n - col = k →
        checkPivot M row col = none →
        ∀ j : Fin n, col ≤ j.val → ∀ r : Fin m, row ≤ r.val → M.get r j = 0 := by
    intro k
    induction k with
    | zero =>
      intro row col hk hnone j hj r hr
      have hcol : n ≤ col := Nat.le_of_sub_eq_zero hk
      have hlt : j.val < col := lt_of_lt_of_le j.isLt hcol
      exact by omega
    | succ k ih =>
      intro row col hk hnone j hj r hr
      rw [checkPivot, checkPivot.scanCol] at hnone
      by_cases hcol : col < n
      · simp only [hcol] at hnone
        cases hscan : checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) row with
        | some p =>
            simp [hscan] at hnone
        | none =>
            have hcol_zero : ∀ r : Fin m, row ≤ r.val → M.get r ⟨col, hcol⟩ = 0 :=
              scanRow_none_col_zero (M := M) col row hcol hscan
            have hnext : checkPivot M row (col + 1) = none := by
              simp only [hscan] at hnone
              exact hnone
            have hj' := lt_or_eq_of_le hj
            cases hj' with
            | inl hjlt =>
                have hk' : n - (col + 1) = k :=
                  by omega
                have hj_ge : col + 1 ≤ j.val := Nat.succ_le_of_lt hjlt
                exact ih row (col + 1) hk' hnext j hj_ge r hr
            | inr hjeq =>
                subst hjeq
                exact hcol_zero r hr
      · have hcol' : n ≤ col := Nat.le_of_not_gt hcol
        have h' : n - col = 0 := Nat.sub_eq_zero_iff_le.mpr hcol'
        rw [hk] at h'
        exact (False.elim ((Nat.ne_of_lt (Nat.succ_pos k)) h'.symm))
  exact hrec (n - col) row col rfl h

/--
If `scanRow` finds a pivot candidate, its row index is greater than or equal to the starting
row used for the scan.
-/
private lemma scanRow_some_row_ge
    (M : DenseMatrix m n α) (col row : Nat) (hcol : col < n)
    {pr : Fin m} {pc : Fin n}
    (h : checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) row = some (pr, pc)) :
    row ≤ pr.val := by
  classical
  have hrec :
      ∀ k row, m - row = k →
        checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) row = some (pr, pc) →
          row ≤ pr.val := by
    intro k
    induction k with
    | zero =>
      intro row hk h
      have hrow : m ≤ row := Nat.le_of_sub_eq_zero hk
      rw [checkPivot.scanCol.scanRow, dif_neg (not_lt_of_ge hrow)] at h
      cases h
    | succ k ih =>
      intro row hk h
      have hrow : row < m := by omega
      rw [checkPivot.scanCol.scanRow, dif_pos hrow] at h
      by_cases hzero : M.get ⟨row, hrow⟩ ⟨col, hcol⟩ ≠ 0
      · simp only [ne_eq, hzero, not_false_eq_true, ↓reduceIte, Option.some.injEq,
        Prod.mk.injEq] at h
        rcases h with ⟨hpr, _⟩
        subst hpr
        exact Nat.le_refl _
      · have hnext :
            checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) (row + 1) = some (pr, pc) := by
          simp only [hzero] at h
          exact h
        have hk' : m - (row + 1) = k :=
          by omega
        have hge : row + 1 ≤ pr.val := ih (row + 1) hk' hnext
        exact Nat.le_trans (Nat.le_succ _) hge
  exact hrec (m - row) row rfl h

/--
Any successful `scanRow` call in column `col` returns that same column index.
-/
private lemma scanRow_some_col_eq
    (M : DenseMatrix m n α) (col row : Nat) (hcol : col < n)
    {pr : Fin m} {pc : Fin n}
    (h : checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) row = some (pr, pc)) :
    pc = ⟨col, hcol⟩ := by
  classical
  have hrec :
      ∀ k row, m - row = k →
        checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) row = some (pr, pc) →
          pc = ⟨col, hcol⟩ := by
    intro k
    induction k with
    | zero =>
      intro row hk h
      have hrow : m ≤ row := Nat.le_of_sub_eq_zero hk
      rw [checkPivot.scanCol.scanRow, dif_neg (not_lt_of_ge hrow)] at h
      cases h
    | succ k ih =>
      intro row hk h
      have hrow : row < m := by omega
      rw [checkPivot.scanCol.scanRow, dif_pos hrow] at h
      by_cases hzero : M.get ⟨row, hrow⟩ ⟨col, hcol⟩ ≠ 0
      · simp only [ne_eq, hzero, not_false_eq_true, ↓reduceIte, Option.some.injEq,
        Prod.mk.injEq] at h
        rcases h with ⟨_, hpc⟩
        exact hpc.symm
      · have hnext :
            checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) (row + 1) = some (pr, pc) := by
          simp only [hzero] at h
          exact h
        have hk' : m - (row + 1) = k :=
          by omega
        exact ih (row + 1) hk' hnext
  exact hrec (m - row) row rfl h

/--
If `checkPivot` returns `some (pr, pc)`, the pivot row `pr` is not above
the starting search row.
-/
lemma checkPivot_some_row_ge
    (M : DenseMatrix m n α) (row col : Nat)
    {pr : Fin m} {pc : Fin n}
    (h : checkPivot M row col = some (pr, pc)) :
    row ≤ pr.val := by
  classical
  have hrec :
      ∀ k row col, n - col = k →
        checkPivot M row col = some (pr, pc) → row ≤ pr.val := by
    intro k
    induction k with
    | zero =>
      intro row col hk h
      have hcol : n ≤ col := Nat.le_of_sub_eq_zero hk
      rw [checkPivot, checkPivot.scanCol, dif_neg (not_lt_of_ge hcol)] at h
      cases h
    | succ k ih =>
      intro row col hk h
      rw [checkPivot, checkPivot.scanCol] at h
      by_cases hcol : col < n
      · simp only [hcol] at h
        cases hscan : checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) row with
        | some p =>
            have h' :
            checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) row = some (pr, pc) := by
              simpa [hscan] using h
            have hrowge := scanRow_some_row_ge (M := M) col row hcol h'
            exact hrowge
        | none =>
            have hnext : checkPivot M row (col + 1) = some (pr, pc) := by
              change checkPivot.scanCol M row (col + 1) = some (pr, pc)
              simpa [hscan] using h
            have hk' : n - (col + 1) = k :=
              by omega
            exact ih row (col + 1) hk' hnext
      · simp [hcol] at h
  exact hrec (n - col) row col rfl h

/--
If `checkPivot M row col = some (pr, pc)`, then every earlier column `j < pc`
with `j ≥ col` is zero below `row`.
-/
lemma checkPivot_some_minimal
    (M : DenseMatrix m n α) (row col : Nat)
    {pr : Fin m} {pc : Fin n}
    (h : checkPivot M row col = some (pr, pc)) :
    ∀ j : Fin n, col ≤ j.val → j < pc → ∀ r : Fin m, row ≤ r.val → M.get r j = 0 := by
  classical
  have hrec :
      ∀ k row col, n - col = k →
        checkPivot M row col = some (pr, pc) →
        ∀ j : Fin n, col ≤ j.val → j < pc → ∀ r : Fin m, row ≤ r.val → M.get r j = 0 := by
    intro k
    induction k with
    | zero =>
      intro row col hk h j hj hlt r hr
      have hcol : n ≤ col := Nat.le_of_sub_eq_zero hk
      have hlt' : j.val < col := lt_of_lt_of_le j.isLt hcol
      exact by omega
    | succ k ih =>
      intro row col hk h j hj hlt r hr
      by_cases hcol : col < n
      · dsimp [checkPivot] at h
        rw [checkPivot.scanCol] at h
        simp only [hcol] at h
        cases hscan : checkPivot.scanCol.scanRow (M := M) col (hcol := hcol) row with
        | some p =>
            have h' : some p = some (pr, pc) := by simpa [hscan] using h
            cases h'
            have hpc : pc = ⟨col, hcol⟩ :=
              scanRow_some_col_eq (M := M) col row hcol hscan
            have hlt' : j.val < col := by simpa [Fin.lt_def, hpc] using hlt
            exact by omega
        | none =>
            have hcol_zero : ∀ r : Fin m, row ≤ r.val → M.get r ⟨col, hcol⟩ = 0 :=
              scanRow_none_col_zero (M := M) col row hcol hscan
            have hnext : checkPivot M row (col + 1) = some (pr, pc) := by
              simpa [checkPivot, hscan] using h
            have hj' := lt_or_eq_of_le hj
            cases hj' with
            | inl hjlt =>
                have hk' : n - (col + 1) = k :=
                  by omega
                have hj_ge : col + 1 ≤ j.val := Nat.succ_le_of_lt hjlt
                exact ih row (col + 1) hk' hnext j hj_ge hlt r hr
            | inr hjeq =>
              subst hjeq
              exact hcol_zero r hr
      · have hcol' : n ≤ col := Nat.le_of_not_gt hcol
        have h' : n - col = 0 := Nat.sub_eq_zero_iff_le.mpr hcol'
        rw [hk] at h'
        exact (False.elim ((Nat.ne_of_lt (Nat.succ_pos k)) h'.symm))
  exact hrec (n - col) row col rfl h

/-- If a pivot was found at entry `(pivotRow, pivotCol)`, then that pivot is nonzero. -/
lemma checkPivot_some_nonzero {pivotRow : Fin m} {pivotCol : Fin n} (M : DenseMatrix m n α)
    (r c : Nat) (h : checkPivot M r c = some (pivotRow, pivotCol))
    : M.get pivotRow pivotCol ≠ 0 := by
  rw [checkPivot, checkPivot.scanCol] at h
  split_ifs at h with h1
  · split at h
    · rename_i x p heq
      rw [checkPivot.scanCol.scanRow] at heq
      split_ifs at heq with h2 h3
      · rw [h] at heq
        injection heq with heq'
        cases heq'
        exact h3
      · have h' : checkPivot M (r + 1) c = some (pivotRow, pivotCol) := by
          rw [checkPivot, checkPivot.scanCol]
          simp_all only [Option.some.injEq, ne_eq, Decidable.not_not, ↓reduceDIte]
        exact checkPivot_some_nonzero M (r + 1) c h'
    · rename_i x heq
      exact checkPivot_some_nonzero M r (c + 1) h

/-! ## `replace` and `eliminateCol` behavior lemmas -/

omit [DecidableEq α] in
/-- `replaceRow` only modifies row `tgt`. -/
private lemma replace_apply_of_ne
    (M : DenseMatrix m n α) (src tgt : Fin m) (k : α)
    (r : Fin m) (j : Fin n) (huse : src ≠ tgt) (hrow : r ≠ tgt) :
    (replaceRow M src tgt k).get r j = M.get r j := by
  simp [replaceRow, huse, hrow, of_apply]

omit [DecidableEq α] in
/-- `replaceRow` adds a multiple of row `src` to row `tgt`. -/
private lemma replace_apply_eq
    (M : DenseMatrix m n α) (src tgt : Fin m) (k : α)
    (huse : src ≠ tgt) (j : Fin n) :
    (replaceRow M src tgt k).get tgt j = M.get tgt j + k * M.get src j := by
  simp [replaceRow, huse, of_apply]

omit [DecidableEq α] in
/--
Using `-M.get tgt pivotCol / M.get pivotRow pivotCol` as the scaling factor for the source
row zeros out the target row.
-/
private lemma replace_pivot_col_zero_of_ne
    (M : DenseMatrix m n α) (pivotRow tgt : Fin m) (pivotCol : Fin n)
    (huse : pivotRow ≠ tgt) (hne : M.get pivotRow pivotCol ≠ 0) :
    (replaceRow M pivotRow tgt (-M.get tgt pivotCol / M.get pivotRow pivotCol)).get tgt pivotCol = 0 := by
  rw [replace_apply_eq (M := M) (src := pivotRow) (tgt := tgt)
    (k := -M.get tgt pivotCol / M.get pivotRow pivotCol) (huse := huse) (j := pivotCol)]
  rw [neg_div, div_eq_mul_inv]
  have hcancel : (M.get pivotRow pivotCol)⁻¹ * M.get pivotRow pivotCol = 1 := inv_mul_cancel₀ hne
  calc
    M.get tgt pivotCol + -(M.get tgt pivotCol * (M.get pivotRow pivotCol)⁻¹) * M.get pivotRow pivotCol
        = M.get tgt pivotCol + -(M.get tgt pivotCol * ((M.get pivotRow pivotCol)⁻¹ * M.get pivotRow pivotCol)) := by
            ring_nf
    _ = M.get tgt pivotCol + -(M.get tgt pivotCol * 1) := by rw [hcancel]
    _ = 0 := by ring

omit [DecidableEq α] in
private lemma replace_pivot_col_zero
    (M : DenseMatrix m n α) (pivotRow tgt : Fin m) (pivotCol : Fin n)
    (huse : pivotRow ≠ tgt) (h1 : M.get pivotRow pivotCol = 1) :
    (replaceRow M pivotRow tgt (-M.get tgt pivotCol / M.get pivotRow pivotCol)).get tgt pivotCol = 0 := by
  exact replace_pivot_col_zero_of_ne (M := M) (pivotRow := pivotRow)
    (tgt := tgt) (pivotCol := pivotCol) huse (by simp [h1])

/--
The matrix output of `eliminateColLoop` is independent of the current `steps`
list; `steps` only records operations.
-/
private theorem eliminateCol_go_matrix_irrel
    (pivotRow : Fin m) (pivotCol : Fin n) (r : Nat)
    (cur : DenseMatrix m n α) (steps₁ steps₂ : List (RowOp m α)) :
    eliminateColLoopMatrix pivotRow pivotCol r cur steps₁ =
      eliminateColLoopMatrix pivotRow pivotCol r cur steps₂ := by
  have hrec :
      ∀ k (r : Nat) (cur : DenseMatrix m n α) (steps₁ steps₂ : List (RowOp m α)),
        m - r = k →
          eliminateColLoopMatrix pivotRow pivotCol r cur steps₁ =
            eliminateColLoopMatrix pivotRow pivotCol r cur steps₂ := by
    intro k
    induction k with
    | zero =>
      intro r cur steps₁ steps₂ hk
      have hr : m ≤ r := Nat.le_of_sub_eq_zero hk
      rw [eliminateColLoopMatrix, eliminateColLoop, eliminateColLoopAux, dif_neg (not_lt_of_ge hr)]
      conv_rhs => rw [eliminateColLoopMatrix, eliminateColLoop, eliminateColLoopAux, dif_neg (not_lt_of_ge hr)]
    | succ k ih =>
      intro r cur steps₁ steps₂ hk
      have hr : r < m := by omega
      have hk' : m - (r + 1) = k :=
        by omega
      rw [eliminateColLoopMatrix, eliminateColLoop, eliminateColLoopAux, dif_pos hr]
      conv_rhs => rw [eliminateColLoopMatrix, eliminateColLoop, eliminateColLoopAux, dif_pos hr]
      by_cases hEq : (⟨r, hr⟩ : Fin m) = pivotRow
      · simpa [hEq, List.concat_eq_append, dite_eq_ite,
          eliminateColLoopMatrix, eliminateColLoop] using
          ih (r + 1) cur steps₁ steps₂ hk'
      · by_cases hzero : cur.get ⟨r, hr⟩ pivotCol = 0
        · simpa [hEq, hzero, List.concat_eq_append, dite_eq_ite,
            eliminateColLoopMatrix, eliminateColLoop] using
            ih (r + 1) cur steps₁ steps₂ hk'
        · let cur' := replaceRow cur pivotRow ⟨r, hr⟩ (-cur.get ⟨r, hr⟩ pivotCol / cur.get pivotRow pivotCol)
          let steps1' := steps₁ ++ [RowOp.replace pivotRow ⟨r, hr⟩ (-cur.get ⟨r, hr⟩ pivotCol / cur.get pivotRow pivotCol)]
          let steps2' := steps₂ ++ [RowOp.replace pivotRow ⟨r, hr⟩ (-cur.get ⟨r, hr⟩ pivotCol / cur.get pivotRow pivotCol)]
          have huse : pivotRow ≠ (⟨r, hr⟩ : Fin m) := by
            intro hpr
            exact hEq hpr.symm
          have hpivot' : cur'.get pivotRow pivotCol = cur.get pivotRow pivotCol := by
            simpa [cur'] using
              replace_apply_of_ne
                (M := cur)
                (src := pivotRow)
                (tgt := ⟨r, hr⟩)
                (k := -cur.get ⟨r, hr⟩ pivotCol / cur.get pivotRow pivotCol)
                (r := pivotRow) (j := pivotCol) (huse := huse) (hrow := huse)
          have hrec' := ih (r + 1) cur' steps1' steps2' hk'
          have hgo1 :
              (eliminateColLoopAux pivotRow pivotCol (cur.get pivotRow pivotCol) (r + 1) cur' steps1').1 =
                eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur' steps1' := by
            simpa [steps1'] using
              eliminateColLoopAux_matrix_eq
                (pivotRow := pivotRow) (pivotCol := pivotCol)
                (pivotVal := cur.get pivotRow pivotCol) (r := r + 1) (cur := cur') (steps := steps1')
                hpivot'
          have hgo2 :
              (eliminateColLoopAux pivotRow pivotCol (cur.get pivotRow pivotCol) (r + 1) cur' steps2').1 =
                eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur' steps2' := by
            simpa [steps2'] using
              eliminateColLoopAux_matrix_eq
                (pivotRow := pivotRow) (pivotCol := pivotCol)
                (pivotVal := cur.get pivotRow pivotCol) (r := r + 1) (cur := cur') (steps := steps2')
                hpivot'
          have hrec'' :
              (eliminateColLoopAux pivotRow pivotCol (cur.get pivotRow pivotCol) (r + 1) cur' steps1').1 =
                (eliminateColLoopAux pivotRow pivotCol (cur.get pivotRow pivotCol) (r + 1) cur' steps2').1 := by
            calc
              (eliminateColLoopAux pivotRow pivotCol (cur.get pivotRow pivotCol) (r + 1) cur' steps1').1
                  = eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur' steps1' := hgo1
              _ = eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur' steps2' := hrec'
              _ = (eliminateColLoopAux pivotRow pivotCol (cur.get pivotRow pivotCol) (r + 1) cur' steps2').1 := hgo2.symm
          simpa [cur', steps1', steps2', hEq, hzero, List.concat_eq_append, dite_eq_ite] using hrec''
  exact hrec (m - r) r cur steps₁ steps₂ rfl

/-- Specialization of `eliminateCol_go_matrix_irrel` to the top-level `eliminateCol`. -/
lemma eliminateCol_matrix_irrel
    (M : DenseMatrix m n α) (pivotRow : Fin m) (pivotCol : Fin n)
    (steps : List (RowOp m α)) :
    (eliminateCol M pivotRow pivotCol steps true).1 = eliminateColM M pivotRow pivotCol := by
  simpa [eliminateColM, eliminateCol] using
    eliminateCol_go_matrix_irrel pivotRow pivotCol 0 M steps List.nil

lemma eliminateCol_matrix_irrel_false
    (M : DenseMatrix m n α) (pivotRow : Fin m) (pivotCol : Fin n)
    (steps : List (RowOp m α)) :
    (eliminateCol M pivotRow pivotCol steps false).1 =
      (eliminateCol M pivotRow pivotCol List.nil false).1 := by
  simpa [eliminateCol] using
    eliminateCol_go_matrix_irrel pivotRow pivotCol pivotRow.val M steps List.nil

/--
If column `j` of `pivotRow` is zero in `cur`, then `eliminateColLoop` preserves
column `j` for every row.
-/
lemma eliminateCol_go_preserves_col
    (cur : DenseMatrix m n α) (pivotRow : Fin m) (pivotCol : Fin n)
    (r : Nat) (steps : List (RowOp m α)) (j : Fin n)
    (hzero : cur.get pivotRow j = 0) :
    ∀ i : Fin m, (eliminateColLoopMatrix pivotRow pivotCol r cur steps).get i j = cur.get i j := by
  classical
  have hrec :
      ∀ k (r : Nat) (cur : DenseMatrix m n α) (steps : List (RowOp m α)), m - r = k →
        cur.get pivotRow j = 0 →
        ∀ i : Fin m, (eliminateColLoopMatrix pivotRow pivotCol r cur steps).get i j = cur.get i j := by
    intro k
    induction k with
    | zero =>
      intro r cur steps hk hzero i
      have hr : m ≤ r := Nat.le_of_sub_eq_zero hk
      rw [eliminateColLoopMatrix, eliminateColLoop, eliminateColLoopAux, dif_neg (not_lt_of_ge hr)]
    | succ k ih =>
      intro r cur steps hk hzero i
      have hr : r < m := by omega
      rw [eliminateColLoopMatrix, eliminateColLoop, eliminateColLoopAux, dif_pos hr]
      by_cases hEq : (⟨r, hr⟩ : Fin m) = pivotRow
      · simp only [hEq]
        have hk' : m - (r + 1) = k :=
          by omega
        exact ih (r + 1) cur steps hk' hzero i
      · by_cases hcoeff : cur.get ⟨r, hr⟩ pivotCol ≠ 0
        · simp only [hEq, ↓reduceDIte, ne_eq, hcoeff, not_false_eq_true, ↓reduceIte]
          have hk' : m - (r + 1) = k :=
            by omega
          let i0 : Fin m := ⟨r, hr⟩
          let cur' := replaceRow cur pivotRow i0 (-cur.get i0 pivotCol / cur.get pivotRow pivotCol)
          have huse : pivotRow ≠ i0 := by
            intro hpr
            exact hEq hpr.symm
          have hzero' : cur'.get pivotRow j = 0 := by
            have h :=
              replace_apply_of_ne
              (M := cur)
              (src := pivotRow)
              (tgt := i0)
              (k := -cur.get i0 pivotCol / cur.get pivotRow pivotCol)
              (r := pivotRow)
              (j := j)
              (huse := huse)
              (hrow := huse)
            have h' : cur'.get pivotRow j = cur.get pivotRow j := by
              simpa [cur'] using h
            simpa [h'] using hzero
          have hpivot' : cur'.get pivotRow pivotCol = cur.get pivotRow pivotCol := by
            simpa [cur'] using
              replace_apply_of_ne
                (M := cur)
                (src := pivotRow)
                (tgt := i0)
                (k := -cur.get i0 pivotCol / cur.get pivotRow pivotCol)
                (r := pivotRow) (j := pivotCol) (huse := huse) (hrow := huse)
          let steps' := List.concat steps (.replace pivotRow i0 (-cur.get i0 pivotCol / cur.get pivotRow pivotCol))
          have hih := ih (r + 1) cur' steps' hk' hzero' i
          have hgo :
              (eliminateColLoopAux pivotRow pivotCol (cur.get pivotRow pivotCol) (r + 1) cur' steps').1 =
                eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur' steps' := by
            simpa [steps'] using
              eliminateColLoopAux_matrix_eq
                (pivotRow := pivotRow) (pivotCol := pivotCol)
                (pivotVal := cur.get pivotRow pivotCol) (r := r + 1) (cur := cur') (steps := steps')
                hpivot'
          have hih' :
              (eliminateColLoopAux pivotRow pivotCol (cur.get pivotRow pivotCol) (r + 1) cur' steps').1.get i j =
                cur'.get i j := by
            calc
              (eliminateColLoopAux pivotRow pivotCol (cur.get pivotRow pivotCol) (r + 1) cur' steps').1.get i j
                  = (eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur' steps').get i j := by
                      simpa using congrArg (fun M => M.get i j) hgo
              _ = cur'.get i j := hih
          have hcur' : cur'.get i j = cur.get i j := by
            by_cases hi : i = i0
            · subst hi
              simp [cur', hzero, mul_zero, add_zero]
            · simpa [cur'] using
                replace_apply_of_ne
                (M := cur)
                (src := pivotRow)
                  (tgt := i0)
                  (k := -cur.get i0 pivotCol / cur.get pivotRow pivotCol)
                  (r := i) (j := j) (huse := huse) (hrow := hi)
          calc
            (eliminateColLoopAux pivotRow pivotCol (cur.get pivotRow pivotCol) (r + 1) cur' steps').1.get i j =
                cur'.get i j := hih'
            _ = cur.get i j := hcur'
        · simp (config := { failIfUnchanged := false }) only [hEq, ↓reduceDIte, hcoeff, ↓reduceIte]
          have hk' : m - (r + 1) = k :=
            by omega
          exact ih (r + 1) cur steps hk' hzero i
  exact hrec (m - r) r cur steps rfl hzero

/--
`eliminateColLoop` never changes the pivot row, regardless of the current
iterator position or step log.
-/
lemma eliminateCol_go_pivotRow
    (cur : DenseMatrix m n α) (pivotRow : Fin m) (pivotCol : Fin n)
    (steps : List (RowOp m α)) :
    ∀ r j, (eliminateColLoopMatrix pivotRow pivotCol r cur steps).get pivotRow j = cur.get pivotRow j := by
  classical
  have hrec :
      ∀ k (r : Nat) (cur : DenseMatrix m n α) (steps : List (RowOp m α)), m - r = k →
        ∀ j, (eliminateColLoopMatrix pivotRow pivotCol r cur steps).get pivotRow j = cur.get pivotRow j := by
    intro k
    induction k with
    | zero =>
      intro r cur steps hk j
      have hr : m ≤ r := Nat.le_of_sub_eq_zero hk
      rw [eliminateColLoopMatrix, eliminateColLoop, eliminateColLoopAux, dif_neg (not_lt_of_ge hr)]
    | succ k ih =>
      intro r cur steps hk j
      have hr : r < m := by omega
      let i0 : Fin m := ⟨r, hr⟩
      by_cases hEq : i0 = pivotRow
      · have hk' : m - (r + 1) = k :=
          by omega
        rw [eliminateColLoopMatrix, eliminateColLoop, eliminateColLoopAux, dif_pos hr]
        simp only [i0, hEq]
        exact ih (r + 1) cur steps hk' j
      · by_cases hcoeff : cur.get i0 pivotCol ≠ 0
        · have hk' : m - (r + 1) = k :=
            by omega
          let cur' := replaceRow cur pivotRow i0 (-cur.get i0 pivotCol / cur.get pivotRow pivotCol)
          have hpivot' : cur'.get pivotRow pivotCol = cur.get pivotRow pivotCol := by
            have huse : pivotRow ≠ i0 := by
              intro hpr
              exact hEq hpr.symm
            simpa [cur'] using
              replace_apply_of_ne
                (M := cur)
                (src := pivotRow)
                (tgt := i0)
                (k := -cur.get i0 pivotCol / cur.get pivotRow pivotCol)
                (r := pivotRow) (j := pivotCol) (huse := huse) (hrow := huse)
          have hpr : cur'.get pivotRow j = cur.get pivotRow j := by
            have huse : pivotRow ≠ i0 := by
              intro hpr
              exact hEq hpr.symm
            have h :=
              replace_apply_of_ne
              (M := cur)
              (src := pivotRow)
              (tgt := i0)
              (k := -cur.get i0 pivotCol / cur.get pivotRow pivotCol)
              (r := pivotRow)
              (j := j)
                  (huse := huse)
                  (hrow := huse)
            simpa [cur'] using h
          let steps' := List.concat steps (.replace pivotRow i0 (-cur.get i0 pivotCol / cur.get pivotRow pivotCol))
          have hih := ih (r + 1) cur' steps' hk' j
          have hgo :
              (eliminateColLoopAux pivotRow pivotCol (cur.get pivotRow pivotCol) (r + 1) cur' steps').1 =
                eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur' steps' := by
            simpa [steps'] using
              eliminateColLoopAux_matrix_eq
                (pivotRow := pivotRow) (pivotCol := pivotCol)
                (pivotVal := cur.get pivotRow pivotCol) (r := r + 1) (cur := cur') (steps := steps')
                hpivot'
          have hstep :
              (eliminateColLoopMatrix pivotRow pivotCol r cur steps).get pivotRow j =
                (eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur'
                  (List.concat steps (.replace pivotRow i0 (-cur.get i0 pivotCol / cur.get pivotRow pivotCol)))).get pivotRow j := by
            rw [eliminateColLoopMatrix, eliminateColLoop, eliminateColLoopAux, dif_pos hr]
            simpa [i0, hEq, hcoeff, cur', steps'] using congrArg (fun M => M.get pivotRow j) hgo
          calc
            (eliminateColLoopMatrix pivotRow pivotCol r cur steps).get pivotRow j
                = (eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur'
                  (List.concat steps (.replace pivotRow i0 (-cur.get i0 pivotCol / cur.get pivotRow pivotCol)))).get pivotRow j := hstep
            _ = cur'.get pivotRow j := hih
            _ = cur.get pivotRow j := hpr
        · have hk' : m - (r + 1) = k :=
            by omega
          have hih := ih (r + 1) cur steps hk' j
          have hgo :
              (eliminateColLoopAux pivotRow pivotCol (cur.get pivotRow pivotCol) (r + 1) cur steps).1 =
                eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur steps := by
            simpa using
              eliminateColLoopAux_matrix_eq
                (pivotRow := pivotRow) (pivotCol := pivotCol)
                (pivotVal := cur.get pivotRow pivotCol) (r := r + 1) (cur := cur) (steps := steps)
                rfl
          have hstep :
              (eliminateColLoopMatrix pivotRow pivotCol r cur steps).get pivotRow j =
                (eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur steps).get pivotRow j := by
            rw [eliminateColLoopMatrix, eliminateColLoop, eliminateColLoopAux, dif_pos hr]
            simpa [i0, hEq, hcoeff] using congrArg (fun M => M.get pivotRow j) hgo
          calc
            (eliminateColLoopMatrix pivotRow pivotCol r cur steps).get pivotRow j
                = (eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur steps).get pivotRow j := hstep
            _ = cur.get pivotRow j := hih
  intro r j
  exact hrec (m - r) r cur steps rfl j

/-- Top-level `eliminateColM` preserves the pivot row entrywise. -/
lemma eliminateCol_pivotRow
    (M : DenseMatrix m n α) (pivotRow : Fin m) (pivotCol : Fin n) :
    ∀ j : Fin n, (eliminateColM M pivotRow pivotCol).get pivotRow j = M.get pivotRow j := by
  intro j
  simpa [eliminateColM, eliminateCol] using
    (eliminateCol_go_pivotRow
      (cur := M) (pivotRow := pivotRow) (pivotCol := pivotCol) (steps := List.nil) 0 j)

lemma eliminateCol_pivotRow_false
    (M : DenseMatrix m n α) (pivotRow : Fin m) (pivotCol : Fin n) :
    ∀ j : Fin n, (eliminateCol M pivotRow pivotCol List.nil false).1.get pivotRow j = M.get pivotRow j := by
  intro j
  simpa [eliminateCol] using
    (eliminateCol_go_pivotRow
      (cur := M) (pivotRow := pivotRow) (pivotCol := pivotCol)
      (steps := List.nil) pivotRow.val j)

/--
Assuming the pivot entry is normalized to `1`, `eliminateColM` zeroes the
pivot column at every non-pivot row.
-/
lemma eliminateCol_pivotCol_zero
    (M : DenseMatrix m n α) (pivotRow : Fin m) (pivotCol : Fin n)
    (h1 : M.get pivotRow pivotCol = 1) :
    ∀ r : Fin m, r ≠ pivotRow → (eliminateColM M pivotRow pivotCol).get r pivotCol = 0 := by
  classical
  intro r hr
  have hrec :
      ∀ k (r : Nat) (cur : DenseMatrix m n α) (steps : List (RowOp m α)),
        m - r = k →
        (∀ i : Fin m, i.val < r → i ≠ pivotRow → cur.get i pivotCol = 0) →
        cur.get pivotRow pivotCol = 1 →
        ∀ i : Fin m, i ≠ pivotRow →
          (eliminateColLoopMatrix pivotRow pivotCol r cur steps).get i pivotCol = 0 := by
    intro k
    induction k with
    | zero =>
      intro r cur steps hk hpre h1 i hi
      have hr : m ≤ r := Nat.le_of_sub_eq_zero hk
      have hir : i.val < r := lt_of_lt_of_le i.isLt hr
      rw [eliminateColLoopMatrix, eliminateColLoop, eliminateColLoopAux, dif_neg (not_lt_of_ge hr)]
      exact hpre i hir hi
    | succ k ih =>
      intro r cur steps hk hpre h1 i hi
      have hr : r < m := by omega
      rw [eliminateColLoopMatrix, eliminateColLoop, eliminateColLoopAux, dif_pos hr]
      let i0 : Fin m := ⟨r, hr⟩
      by_cases hi0 : i0 = pivotRow
      · simp only [i0, hi0]
        have hk' : m - (r + 1) = k :=
          by omega
        have hpre' :
            ∀ i : Fin m, i.val < r + 1 → i ≠ pivotRow → cur.get i pivotCol = 0 := by
          intro i hi' hne
          have hle : i.val ≤ r := Nat.lt_succ_iff.mp hi'
          by_cases hir : i.val < r
          · exact hpre i hir hne
          · have hEq : i.val = r := le_antisymm hle (le_of_not_gt hir)
            have : i = i0 := by
              ext
              simp [hEq, i0]
            exact (False.elim (hne (by simp [this, hi0])))
        exact ih (r + 1) cur steps hk' hpre' h1 i hi
      · simp only [i0, hi0]
        by_cases hcoeff : cur.get i0 pivotCol ≠ 0
        · have hk' : m - (r + 1) = k :=
            by omega
          let cur' := replaceRow cur pivotRow i0 (-cur.get i0 pivotCol / cur.get pivotRow pivotCol)
          have huse : pivotRow ≠ i0 := by
            intro hpr
            exact hi0 hpr.symm
          have h1' : cur'.get pivotRow pivotCol = 1 := by
            simp [cur', replaceRow, huse, of_apply, h1]
          have hpivot' : cur'.get pivotRow pivotCol = cur.get pivotRow pivotCol := by
            calc
              cur'.get pivotRow pivotCol = 1 := h1'
              _ = cur.get pivotRow pivotCol := by simp [h1]
          have hpre' :
              ∀ i : Fin m, i.val < r + 1 → i ≠ pivotRow → cur'.get i pivotCol = 0 := by
            intro i hi' hne
            have hle : i.val ≤ r := Nat.lt_succ_iff.mp hi'
            by_cases hir : i.val < r
            · have hne' : i ≠ i0 := by
                intro hEq
                have : i.val = r := by simpa [i0] using congrArg Fin.val hEq
                exact (Nat.lt_irrefl _ (this ▸ hir))
              simp [cur', replaceRow, huse, hne', of_apply, hpre i hir hne]
            · have hEq : i.val = r := le_antisymm hle (le_of_not_gt hir)
              have hEq' : i = i0 := by
                ext
                simp [hEq, i0]
              subst hEq'
              have hzero :=
                replace_pivot_col_zero (M := cur) (pivotRow := pivotRow) (tgt := i0)
                  (pivotCol := pivotCol) (huse := huse) h1
              exact hzero
          let steps' := List.concat steps (.replace pivotRow i0 (-cur.get i0 pivotCol / cur.get pivotRow pivotCol))
          have hih := ih (r + 1) cur' steps' hk' hpre' h1' i hi
          have hgo :
              (eliminateColLoopAux pivotRow pivotCol (cur.get pivotRow pivotCol) (r + 1) cur' steps').1 =
                eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur' steps' := by
            simpa [steps'] using
              eliminateColLoopAux_matrix_eq
                (pivotRow := pivotRow) (pivotCol := pivotCol)
                (pivotVal := cur.get pivotRow pivotCol) (r := r + 1) (cur := cur') (steps := steps')
                hpivot'
          have hih' :
              (eliminateColLoopAux pivotRow pivotCol (cur.get pivotRow pivotCol) (r + 1) cur' steps').1.get
                i pivotCol = 0 := by
            calc
              (eliminateColLoopAux pivotRow pivotCol (cur.get pivotRow pivotCol) (r + 1) cur' steps').1.get
                  i pivotCol = (eliminateColLoopMatrix pivotRow pivotCol (r + 1) cur' steps').get i pivotCol := by
                    simpa using congrArg (fun M => M.get i pivotCol) hgo
              _ = 0 := hih
          simpa [i0, hi0, hcoeff, cur', steps'] using hih'
        · have hk' : m - (r + 1) = k :=
            by omega
          have hcoeff' : cur.get i0 pivotCol = 0 := by
            by_contra hne; exact hcoeff hne
          have hpre' :
              ∀ i : Fin m, i.val < r + 1 → i ≠ pivotRow → cur.get i pivotCol = 0 := by
            intro i hi' hne
            have hle : i.val ≤ r := Nat.lt_succ_iff.mp hi'
            by_cases hir : i.val < r
            · exact hpre i hir hne
            · have hEq : i.val = r := le_antisymm hle (le_of_not_gt hir)
              have hEq' : i = i0 := by
                ext
                simp [hEq, i0]
              subst hEq'
              exact hcoeff'
          have hih := ih (r + 1) cur steps hk' hpre' h1 i hi
          simpa [i0, hi0, hcoeff', eliminateColLoopMatrix,
            eliminateColLoop] using hih
  have hpre0 : ∀ i : Fin m, i.val < 0 → i ≠ pivotRow → M.get i pivotCol = 0 := by
    intro i hi
    exact (False.elim (Nat.not_lt_zero _ hi))
  have hrec' := hrec (m - 0) 0 M List.nil rfl hpre0 h1
  simpa [eliminateColM, eliminateCol] using hrec' r hr

/--
Assuming the pivot entry is nonzero, `eliminateCol` with `reduced = false`
zeroes the pivot column at every row strictly below the pivot.
-/
lemma eliminateCol_below_pivotCol_zero
    (M : DenseMatrix m n α) (pivotRow : Fin m) (pivotCol : Fin n)
    (hne : M.get pivotRow pivotCol ≠ 0) :
    ∀ r : Fin m, pivotRow.val < r.val →
      (eliminateCol M pivotRow pivotCol List.nil false).1.get r pivotCol = 0 := by
  classical
  intro r hr
  have hrec :
      ∀ k (r0 : Nat) (cur : DenseMatrix m n α) (steps : List (RowOp m α)),
        m - r0 = k →
        (∀ i : Fin m, pivotRow.val < i.val → i.val < r0 → cur.get i pivotCol = 0) →
        cur.get pivotRow pivotCol ≠ 0 →
        ∀ i : Fin m, pivotRow.val < i.val →
          (eliminateColLoopMatrix pivotRow pivotCol r0 cur steps).get i pivotCol = 0 := by
    intro k
    induction k with
    | zero =>
        intro r0 cur steps hk hpre hpivot i hi
        have hr0 : m ≤ r0 := Nat.le_of_sub_eq_zero hk
        have hii : i.val < r0 := lt_of_lt_of_le i.isLt hr0
        rw [eliminateColLoopMatrix, eliminateColLoop, eliminateColLoopAux,
          dif_neg (not_lt_of_ge hr0)]
        exact hpre i hi hii
    | succ k ih =>
        intro r0 cur steps hk hpre hpivot i hi
        have hr0 : r0 < m := by omega
        rw [eliminateColLoopMatrix, eliminateColLoop, eliminateColLoopAux, dif_pos hr0]
        let i0 : Fin m := ⟨r0, hr0⟩
        by_cases hi0 : i0 = pivotRow
        · have hk' : m - (r0 + 1) = k := by omega
          have hpre' :
              ∀ i : Fin m, pivotRow.val < i.val → i.val < r0 + 1 → cur.get i pivotCol = 0 := by
            intro i hi' hir'
            have hir : i.val < r0 := by
              by_cases hEq : i.val = r0
              · exfalso
                have hp : pivotRow.val = r0 := by simpa [i0] using congrArg Fin.val hi0.symm
                simp [hEq, hp] at hi'
              · omega
            exact hpre i hi' hir
          simpa [i0, hi0, eliminateColLoopMatrix,
            eliminateColLoop] using
            ih (r0 + 1) cur steps hk' hpre' hpivot i hi
        · by_cases hcoeff : cur.get i0 pivotCol ≠ 0
          · have hk' : m - (r0 + 1) = k := by omega
            let cur' := replaceRow cur pivotRow i0 (-cur.get i0 pivotCol / cur.get pivotRow pivotCol)
            let steps' := List.concat steps (.replace pivotRow i0 (-cur.get i0 pivotCol / cur.get pivotRow pivotCol))
            have huse : pivotRow ≠ i0 := by
              intro hpr
              exact hi0 hpr.symm
            have hpivot' : cur'.get pivotRow pivotCol = cur.get pivotRow pivotCol := by
              simpa [cur'] using
                replace_apply_of_ne
                  (M := cur) (src := pivotRow) (tgt := i0)
                  (k := -cur.get i0 pivotCol / cur.get pivotRow pivotCol)
                  (r := pivotRow) (j := pivotCol) (huse := huse) (hrow := huse)
            have hpre' :
                ∀ i : Fin m, pivotRow.val < i.val → i.val < r0 + 1 → cur'.get i pivotCol = 0 := by
              intro i hi' hir'
              have hle : i.val ≤ r0 := Nat.lt_succ_iff.mp hir'
              by_cases hir : i.val < r0
              · have hne : i ≠ i0 := by
                  intro hEq
                  have : i.val = r0 := by simpa [i0] using congrArg Fin.val hEq
                  exact (Nat.lt_irrefl _ (this ▸ hir))
                simp [cur', replaceRow, huse, hne, of_apply, hpre i hi' hir]
              · have hEq : i.val = r0 := le_antisymm hle (le_of_not_gt hir)
                have hEq' : i = i0 := by
                  ext
                  simp [hEq, i0]
                subst hEq'
                exact replace_pivot_col_zero_of_ne
                  (M := cur) (pivotRow := pivotRow) (tgt := i0)
                  (pivotCol := pivotCol) huse hpivot
            have hgo :
                (eliminateColLoopAux pivotRow pivotCol (cur.get pivotRow pivotCol) (r0 + 1) cur' steps').1 =
                  eliminateColLoopMatrix pivotRow pivotCol (r0 + 1) cur' steps' := by
              simpa [steps'] using
                eliminateColLoopAux_matrix_eq
                  (pivotRow := pivotRow) (pivotCol := pivotCol)
                  (pivotVal := cur.get pivotRow pivotCol) (r := r0 + 1) (cur := cur') (steps := steps')
                  hpivot'
            have hih := ih (r0 + 1) cur' steps' hk' hpre' (by simpa [hpivot'] using hpivot) i hi
            have hih' :
                (eliminateColLoopAux pivotRow pivotCol (cur.get pivotRow pivotCol) (r0 + 1) cur' steps').1.get i pivotCol = 0 := by
              calc
                (eliminateColLoopAux pivotRow pivotCol (cur.get pivotRow pivotCol) (r0 + 1) cur' steps').1.get i pivotCol
                    = (eliminateColLoopMatrix pivotRow pivotCol (r0 + 1) cur' steps').get i pivotCol := by
                        simpa using congrArg (fun M => M.get i pivotCol) hgo
                _ = 0 := hih
            simpa [i0, hi0, hcoeff, cur', steps'] using hih'
          · have hk' : m - (r0 + 1) = k := by omega
            have hcoeff' : cur.get i0 pivotCol = 0 := by
              by_contra hne'
              exact hcoeff hne'
            have hpre' :
                ∀ i : Fin m, pivotRow.val < i.val → i.val < r0 + 1 → cur.get i pivotCol = 0 := by
              intro i hi' hir'
              have hle : i.val ≤ r0 := Nat.lt_succ_iff.mp hir'
              by_cases hir : i.val < r0
              · exact hpre i hi' hir
              · have hEq : i.val = r0 := le_antisymm hle (le_of_not_gt hir)
                have hEq' : i = i0 := by
                  ext
                  simp [hEq, i0]
                subst hEq'
                exact hcoeff'
            have hih := ih (r0 + 1) cur steps hk' hpre' hpivot i hi
            simpa [i0, hi0, hcoeff', eliminateColLoopMatrix,
              eliminateColLoop] using hih
  have hpre0 : ∀ i : Fin m, pivotRow.val < i.val → i.val < pivotRow.val → M.get i pivotCol = 0 := by
    intro i hi hlt
    exact (False.elim (Nat.not_lt_of_ge (le_of_lt hi) hlt))
  have hrec' := hrec (m - pivotRow.1) pivotRow.1 M List.nil rfl hpre0 hne r hr
  simpa [eliminateColLoopMatrix, eliminateCol] using hrec'

end DenseMatrix
