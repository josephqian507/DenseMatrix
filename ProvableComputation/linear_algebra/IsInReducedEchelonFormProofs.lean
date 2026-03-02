import ProvableComputation.linear_algebra.EchelonCommonProofs

namespace Matrix

variable {R : Type} [Field R] [DecidableEq R]
variable {m n : ℕ}

private lemma fin_eq_of_val_eq {n : ℕ} {i : Fin n} {k : ℕ} (hk : k < n) (h : i.1 = k) :
    i = ⟨k, hk⟩ := by
  ext
  exact h

/-- Matrix output of `rrefAux` when starting from an empty step log. -/
abbrev rrefAuxM
    (M : Matrix (Fin m) (Fin n) R) (row col : Nat) (steps : List (RowOp m R)) :
    Matrix (Fin m) (Fin n) R :=
  (rrefAux M row col steps true).1

/-! Echelon invariants. -/

structure EchelonStateCore (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n) : Prop where
  row_le : row ≤ m
  bound_le : bound ≤ n
  col_le : col ≤ bound
  pivot_row : ∀ i hi, IsPivot M i (pivs i hi)
  pivot_strict : ∀ i j hi hj, i.1 < j.1 → pivs i hi < pivs j hj
  pivot_lt_bound : ∀ i hi, (pivs i hi).1 < bound
  cols_lt_bound_zero :
    ∀ r : Fin m, row ≤ r.1 → ∀ j : Fin n, j.1 < bound → M r j = 0

structure ReducedStateExtras (M : Matrix (Fin m) (Fin n) R) (row : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n) : Prop where
  pivot_one : ∀ i hi, M i (pivs i hi) = 1
  pivot_col_zero : ∀ i hi r, r ≠ i → M r (pivs i hi) = 0

structure EchelonState (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n) : Prop extends
    EchelonStateCore (M := M) row col bound pivs,
    ReducedStateExtras (M := M) row pivs

private def mkEchelonState
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (row_le : row ≤ m)
    (bound_le : bound ≤ n)
    (col_le : col ≤ bound)
    (pivot_row : ∀ i hi, IsPivot M i (pivs i hi))
    (pivot_strict : ∀ i j hi hj, i.1 < j.1 → pivs i hi < pivs j hj)
    (pivot_lt_bound : ∀ i hi, (pivs i hi).1 < bound)
    (cols_lt_bound_zero :
      ∀ r : Fin m, row ≤ r.1 → ∀ j : Fin n, j.1 < bound → M r j = 0)
    (pivot_one : ∀ i hi, M i (pivs i hi) = 1)
    (pivot_col_zero : ∀ i hi r, r ≠ i → M r (pivs i hi) = 0) :
    EchelonState (M := M) row col bound pivs :=
  { toEchelonStateCore := {
      row_le := row_le
      bound_le := bound_le
      col_le := col_le
      pivot_row := pivot_row
      pivot_strict := pivot_strict
      pivot_lt_bound := pivot_lt_bound
      cols_lt_bound_zero := cols_lt_bound_zero
    }
    toReducedStateExtras := {
      pivot_one := pivot_one
      pivot_col_zero := pivot_col_zero
    }
  }

omit [DecidableEq R] in
lemma echelon_of_state
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hcore : EchelonStateCore (M := M) row col bound pivs)
    (hzero : ∀ r : Fin m, row ≤ r.1 → RowIsZero M r) :
    IsEchelonForm (M := M) := by
  classical
  refine IsEchelonForm.mk ?row_zero_or_pivot ?zero_rows_bottom ?pivots_strict
  · intro i
    by_cases hi : i.1 < row
    · right
      refine ⟨pivs i hi, hcore.pivot_row i hi⟩
    · left
      have hi' : row ≤ i.1 := by omega
      exact hzero i hi'
  · intro i j hij hzi
    by_cases hi : i.1 < row
    · have : False := RowIsZero.not_isPivot (M := M) (i := i)
        (p := pivs i hi) hzi (hcore.pivot_row i hi)
      exact (False.elim this)
    · have hi' : row ≤ i.1 := by omega
      have hj' : row ≤ j.1 := le_trans hi' (le_of_lt hij)
      exact hzero j hj'
  · intro i j p q hij hp hq
    by_cases hi : i.1 < row
    · by_cases hj : j.1 < row
      · have hp' : p = pivs i hi := IsPivot.eq_of_left hp (hcore.pivot_row i hi)
        have hq' : q = pivs j hj := IsPivot.eq_of_left hq (hcore.pivot_row j hj)
        subst hp'; subst hq'
        exact hcore.pivot_strict i j hi hj (by simpa using hij)
      · have hj' : row ≤ j.1 := by omega
        have hz : RowIsZero M j := hzero j hj'
        exact (False.elim (RowIsZero.not_isPivot (M := M) (i := j) (p := q) hz hq))
    · have hi' : row ≤ i.1 := by omega
      have hz : RowIsZero M i := hzero i hi'
      exact (False.elim (RowIsZero.not_isPivot (M := M) (i := i) (p := p) hz hp))

omit [DecidableEq R] in
lemma reduced_of_state
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hcore : EchelonStateCore (M := M) row col bound pivs)
    (hextras : ReducedStateExtras (M := M) row pivs)
    (hzero : ∀ r : Fin m, row ≤ r.1 → RowIsZero M r) :
    IsReducedEchelonForm (M := M) := by
  classical
  refine IsReducedEchelonForm.mk ?echelon ?pivot_is_one ?pivot_col_zero_above
  · exact echelon_of_state (M := M) row col bound pivs hcore hzero
  · intro i p hp
    by_cases hi : i.1 < row
    · have hp' : p = pivs i hi := IsPivot.eq_of_left hp (hcore.pivot_row i hi)
      subst hp'
      exact hextras.pivot_one i hi
    · have hi' : row ≤ i.1 := by omega
      have hz : RowIsZero M i := hzero i hi'
      exact (False.elim (RowIsZero.not_isPivot (M := M) (i := i) (p := p) hz hp))
  · intro i r p hr hp
    by_cases hi : i.1 < row
    · have hp' : p = pivs i hi := IsPivot.eq_of_left hp (hcore.pivot_row i hi)
      subst hp'
      have hrne : r ≠ i := by
        intro hEq
        cases hEq
        exact lt_irrefl _ hr
      exact hextras.pivot_col_zero i hi r hrne
    · have hi' : row ≤ i.1 := by omega
      have hz : RowIsZero M i := hzero i hi'
      exact (False.elim (RowIsZero.not_isPivot (M := M) (i := i) (p := p) hz hp))

omit [DecidableEq R] in
private lemma zero_rows_of_row_ge
    (M : Matrix (Fin m) (Fin n) R) (row : Nat) (hrow : m ≤ row) :
    ∀ r : Fin m, row ≤ r.1 → RowIsZero M r := by
  intro r hr
  have hlt : r.1 < row := lt_of_lt_of_le r.2 hrow
  exact False.elim ((Nat.not_lt_of_ge hr) hlt)

private lemma zero_rows_of_checkPivot_none
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonState (M := M) row col bound pivs)
    (hnone : checkPivot M row col = none) :
    ∀ r : Fin m, row ≤ r.1 → RowIsZero M r := by
  intro r hr j
  by_cases hjb : j.1 < bound
  · exact hstate.cols_lt_bound_zero r hr j hjb
  · have hjc : col ≤ j.1 := by
      have : bound ≤ j.1 := by omega
      exact le_trans hstate.col_le this
    exact checkPivot_none_zero (M := M) row col hnone j hjc r hr

omit [DecidableEq R] in
private lemma zero_rows_of_col_ge
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonState (M := M) row col bound pivs)
    (hcol : ¬ col < n) :
    ∀ r : Fin m, row ≤ r.1 → RowIsZero M r := by
  intro r hr j
  have hbound : bound = n := by
    have hcolle : col ≤ bound := hstate.col_le
    have hboundle : bound ≤ n := hstate.bound_le
    omega
  have hj : j.1 < bound := by
    rw [hbound]
    exact j.2
  exact hstate.cols_lt_bound_zero r hr j hj

omit [DecidableEq R] in
private def emptyPivs :
    ∀ i : Fin m, i.1 < 0 → Fin n := by
  intro _ hi
  omega

omit [DecidableEq R] in
private lemma initial_state (M : Matrix (Fin m) (Fin n) R) :
    EchelonState (M := M) (row := 0) (col := 0) (bound := 0) emptyPivs := by
  refine mkEchelonState (M := M) (row := 0) (col := 0) (bound := 0) (pivs := emptyPivs)
    ?row_le ?bound_le
    ?col_le ?pivot_row
    ?pivot_strict
    ?pivot_lt_bound
    ?cols_zero
    ?pivot_one
    ?pivot_col_zero
  · omega
  · omega
  · omega
  · intro i hi; omega
  · intro i j hi hj hij; omega
  · intro i hi; omega
  · intro r hr j hj; omega
  · intro i hi; omega
  · intro i hi r hr; omega

/-! Step lemma: update state after a pivot. -/

private def extendPivs (row : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (pivotCol : Fin n) :
    ∀ i : Fin m, i.1 < row + 1 → Fin n :=
  fun i _ =>
    if hlt : i.1 < row then pivs i hlt else pivotCol

private lemma pivotCol_ge_bound
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonState (M := M) row col bound pivs)
    {pr : Fin m} {pc : Fin n} (h : checkPivot M row col = some (pr, pc)) :
    bound ≤ pc.1 := by
  by_contra hlt
  have hlt' : pc.1 < bound := lt_of_not_ge hlt
  have hrow : row ≤ pr.1 := checkPivot_some_row_ge (M := M) row col h
  have hzero : M pr pc = 0 :=
    hstate.cols_lt_bound_zero pr hrow pc (by simpa using hlt')
  exact (checkPivot_some_nonzero (M := M) row col h) hzero

private lemma pivot_row_zero_left
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonState (M := M) row col bound pivs)
    {pr : Fin m} {pc : Fin n} (h : checkPivot M row col = some (pr, pc)) :
    ∀ j : Fin n, j < pc → M pr j = 0 := by
  intro j hj
  have hrow : row ≤ pr.1 := checkPivot_some_row_ge (M := M) row col h
  have hbound : bound ≤ pc.1 := pivotCol_ge_bound (M := M) row col bound pivs hstate h
  have hj' : j.1 < bound ∨ col ≤ j.1 := by
    by_cases h1 : j.1 < bound
    · left; exact h1
    · right
      have : bound ≤ j.1 := by omega
      exact le_trans (hstate.col_le) this
  cases hj' with
  | inl hlt =>
      exact hstate.cols_lt_bound_zero pr hrow j hlt
  | inr hge =>
      exact checkPivot_some_minimal (M := M) row col h j hge hj pr hrow

omit [DecidableEq R] in
private lemma isPivot_swap_of_ne
    (M : Matrix (Fin m) (Fin n) R) (i r₁ r₂ : Fin m) (p : Fin n)
    (h1 : i ≠ r₁) (h2 : i ≠ r₂) :
    IsPivot M i p → IsPivot (swapRow M r₁ r₂) i p := by
  intro hp
  refine ⟨?h0, ?hleft⟩
  · -- pivot entry unchanged
    simp [swapRow, of_apply, h1, h2, hp.1]
  · intro j hj
    simp [swapRow, of_apply, h1, h2, hp.2 j hj]

omit [DecidableEq R] in
private lemma isPivot_factor_of_ne
    (M : Matrix (Fin m) (Fin n) R) (i r : Fin m) (p : Fin n) (s : R)
    (h : i ≠ r) :
    IsPivot M i p → IsPivot (factor M r s) i p := by
  intro hp
  refine ⟨?h0, ?hleft⟩
  · simp [factor, of_apply, h, hp.1]
  · intro j hj
    simp [factor, of_apply, h, hp.2 j hj]

private lemma isPivot_eliminate_preserve
    (M : Matrix (Fin m) (Fin n) R) (pivotRow : Fin m) (pivotCol : Fin n)
    {i : Fin m} {p : Fin n} (hp : IsPivot M i p)
    (hzero : ∀ j : Fin n, j < pivotCol → M pivotRow j = 0) (hp_lt : p < pivotCol) :
    IsPivot (eliminateColM M pivotRow pivotCol) i p := by
  classical
  -- elimination only replaces rows using pivotRow; columns < pivotCol stay unchanged
  -- so the pivot remains
  have hpres : ∀ j : Fin n, j < pivotCol →
      (eliminateColM M pivotRow pivotCol) i j = M i j := by
    intro j hj
    -- use preservation of column j
    simpa [eliminateColM, eliminateCol] using
      (eliminateCol_go_preserves_col (cur := M) (pivotRow := pivotRow)
        (pivotCol := pivotCol) (r := 0) (steps := List.nil) (j := j) (hzero := hzero j hj) i)
  refine ⟨?h0, ?hleft⟩
  · have h0 := hpres p hp_lt
    simpa [h0] using hp.1
  · intro j hj
    have h0 := hpres j (lt_of_lt_of_le hj (le_of_lt hp_lt))
    simpa [h0] using hp.2 j hj

omit [DecidableEq R] in
private lemma pivot_lt_newPivot
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonState (M := M) row col bound pivs)
    {pc : Fin n} (hbound : bound ≤ pc.1)
    (i : Fin m) (hlt : i.1 < row) :
    pivs i hlt < pc := by
  have hltb : (pivs i hlt).1 < bound := hstate.pivot_lt_bound i hlt
  have hltpc : (pivs i hlt).1 < pc.1 := lt_of_lt_of_le hltb hbound
  simpa using hltpc

private lemma step_pivot_row
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonState (M := M) row col bound pivs)
    (hrow : row < m) {pr : Fin m} {pc : Fin n}
    (hbound : bound ≤ pc.1) (hpr_ge : row ≤ pr.1) :
    let m1 := if pr.1 = row then M else swapRow M ⟨row, hrow⟩ pr
    let pivotVal : R := m1 ⟨row, hrow⟩ pc
    let m2 := if pivotVal = 1 then m1 else factor m1 ⟨row, hrow⟩ (pivotVal)⁻¹
    let m3 := eliminateColM m2 ⟨row, hrow⟩ pc
    (∀ j : Fin n, j < pc → m2 ⟨row, hrow⟩ j = 0) →
    (∀ j : Fin n, m3 ⟨row, hrow⟩ j = m2 ⟨row, hrow⟩ j) →
    m2 ⟨row, hrow⟩ pc = 1 →
    ∀ i : Fin m, ∀ hi : i.1 < row + 1, IsPivot m3 i ((extendPivs row pivs pc) i hi) := by
  intro m1 pivotVal m2 m3 hzero_left_m2 hrow_unchanged h1 i hi
  by_cases hlt : i.1 < row
  · have hp : IsPivot M i (pivs i hlt) := hstate.pivot_row i hlt
    have hne1 : i ≠ ⟨row, hrow⟩ := by
      intro hEq
      have : i.1 = row := by simpa using congrArg Fin.val hEq
      exact (lt_irrefl _ (this ▸ hlt))
    have hne2 : i ≠ pr := by
      have hltpr : i.1 < pr.1 := by omega
      intro hEq
      have : i.1 = pr.1 := by simpa using congrArg Fin.val hEq
      exact (lt_irrefl _ (this ▸ hltpr))
    have hp1 : IsPivot m1 i (pivs i hlt) := by
      by_cases hpr : pr.1 = row
      · simpa [m1, hpr] using hp
      · have hp' :=
          isPivot_swap_of_ne (M := M) (i := i) (r₁ := ⟨row, hrow⟩) (r₂ := pr)
            (p := pivs i hlt) hne1 hne2 hp
        simpa [m1, hpr] using hp'
    have hp2 : IsPivot m2 i (pivs i hlt) := by
      by_cases hpv : pivotVal = 1
      · simpa [m2, hpv] using hp1
      · have hp2' : IsPivot (factor m1 ⟨row, hrow⟩ pivotVal⁻¹) i (pivs i hlt) :=
          isPivot_factor_of_ne (M := m1) (i := i) (r := ⟨row, hrow⟩)
            (p := pivs i hlt) (s := pivotVal⁻¹) hne1 hp1
        simpa [m2, hpv] using hp2'
    have hp_lt : pivs i hlt < pc :=
      pivot_lt_newPivot (M := M) row col bound pivs hstate (pc := pc) hbound i hlt
    have hp3 : IsPivot m3 i (pivs i hlt) :=
      isPivot_eliminate_preserve (M := m2) (pivotRow := ⟨row, hrow⟩) (pivotCol := pc)
        (p := pivs i hlt) (hp := hp2) (hzero := hzero_left_m2) hp_lt
    simpa [extendPivs, hlt] using hp3
  · have hi_le : i.1 ≤ row := by omega
    have hi_eq : i.1 = row := by omega
    have hrowi : i = ⟨row, hrow⟩ := fin_eq_of_val_eq hrow hi_eq
    subst hrowi
    have hp : IsPivot m3 ⟨row, hrow⟩ pc := by
      refine ⟨?h0, ?hleft⟩
      · have hrowpc : m3 ⟨row, hrow⟩ pc = 1 := by
          have := hrow_unchanged pc
          simp only [h1] at this
          exact this
        simp [hrowpc]
      · intro j hj
        have := hrow_unchanged j
        have h0 := hzero_left_m2 j hj
        simp only [h0] at this
        exact this
    simpa [extendPivs, hlt, hi_eq] using hp

omit [DecidableEq R] in
private lemma step_pivot_strict
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonState (M := M) row col bound pivs)
    {pc : Fin n} (hbound : bound ≤ pc.1) :
    ∀ i j : Fin m, ∀ hi : i.1 < row + 1, ∀ hj : j.1 < row + 1,
      i.1 < j.1 → (extendPivs row pivs pc i hi) < (extendPivs row pivs pc j hj) := by
  intro i j hi hj hij
  by_cases hi' : i.1 < row
  · by_cases hj' : j.1 < row
    · have hp_lt := hstate.pivot_strict i j hi' hj' hij
      simpa [extendPivs, hi', hj'] using hp_lt
    · have hj_le : j.1 ≤ row := by omega
      have hj_eq : j.1 = row := by omega
      have hp_lt : pivs i hi' < pc :=
        pivot_lt_newPivot (M := M) row col bound pivs hstate (pc := pc) hbound i hi'
      simpa [extendPivs, hi', hj_eq] using hp_lt
  · have hi_le : i.1 ≤ row := by omega
    have hi_eq : i.1 = row := by omega
    have hj_le : j.1 ≤ row := by omega
    have hlt' : row < j.1 := by
      simpa [hi_eq] using hij
    exact (False.elim (not_lt_of_ge hj_le hlt'))

omit [DecidableEq R] in
private lemma step_pivot_lt_bound
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonState (M := M) row col bound pivs)
    {pc : Fin n} (hbound : bound ≤ pc.1) :
    ∀ i : Fin m, ∀ hi : i.1 < row + 1, ((extendPivs row pivs pc i hi).1 < pc.1 + 1) := by
  intro i hi
  by_cases hi' : i.1 < row
  · have hltpc : (pivs i hi').1 < pc.1 := by
      simpa using (pivot_lt_newPivot (M := M) row col bound pivs hstate (pc := pc) hbound i hi')
    have hlt' : (pivs i hi').1 < pc.1 + 1 := by omega
    simp [extendPivs, hi', hlt']
  · have hi_eq : i.1 = row := by
      have hi_le : i.1 ≤ row := by omega
      exact le_antisymm hi_le (by omega)
    have hlt' : pc.1 < pc.1 + 1 := by omega
    simp [extendPivs, hi', hlt']

private lemma step_cols_lt_bound_zero
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonState (M := M) row col bound pivs)
    (hrow : row < m) {pr : Fin m} {pc : Fin n}
    (h : checkPivot M row col = some (pr, pc))
    (hbound : bound ≤ pc.1) :
    let m1 := if pr.1 = row then M else swapRow M ⟨row, hrow⟩ pr
    let pivotVal : R := m1 ⟨row, hrow⟩ pc
    let m2 := if pivotVal = 1 then m1 else factor m1 ⟨row, hrow⟩ (pivotVal)⁻¹
    let m3 := eliminateColM m2 ⟨row, hrow⟩ pc
    (∀ j : Fin n, j < pc → m2 ⟨row, hrow⟩ j = 0) →
    m2 ⟨row, hrow⟩ pc = 1 →
    ∀ r : Fin m, row + 1 ≤ r.1 → ∀ j : Fin n, j.1 < pc.1 + 1 → m3 r j = 0 := by
  intro m1 pivotVal m2 m3 hzero_left_m2 h1 r hr j hj
  have hr_ge : row ≤ r.1 := by omega
  have hrrow : r ≠ ⟨row, hrow⟩ := by
    intro hEq
    cases hEq
    exact (Nat.not_succ_le_self _ hr)
  have hcol' : j.1 < pc.1 ∨ j.1 = pc.1 := by
    omega
  cases hcol' with
  | inl hjlt =>
      have hjlt' : j < pc := by
        exact hjlt
      have hzeroM : ∀ r : Fin m, row ≤ r.1 → M r j = 0 := by
        intro r hr'
        by_cases hjb : j.1 < bound
        · exact hstate.cols_lt_bound_zero r hr' j hjb
        · have hjc : col ≤ j.1 := by
            have hb : bound ≤ j.1 := le_of_not_gt hjb
            exact le_trans hstate.col_le hb
          exact checkPivot_some_minimal (M := M) row col h j hjc (by simpa using hjlt) r hr'
      have hm1r : m1 r j = 0 := by
        by_cases hpr : pr.1 = row
        · simp [m1, hpr, hzeroM r hr_ge]
        · by_cases hrpr : r = pr
          · have hnepr : pr ≠ ⟨row, hrow⟩ := by
              intro hEq
              exact hpr (by simpa using congrArg Fin.val hEq)
            simp [m1, hpr, swapRow, of_apply, hrpr, hnepr,
              hzeroM ⟨row, hrow⟩ (Nat.le_refl _)]
          · simp [m1, hpr, swapRow, of_apply, hrpr, hrrow, hzeroM r hr_ge]
      exact
        (calc
          m3 r j = m2 r j := by
            simpa [m3] using
              (eliminateCol_go_preserves_col (cur := m2) (pivotRow := ⟨row, hrow⟩)
                (pivotCol := pc) (r := 0) (steps := List.nil) (j := j)
                (hzero := hzero_left_m2 j hjlt') r)
          _ = 0 := by
            by_cases hpv : pivotVal = 1
            · simp [m2, hpv, hm1r]
            · simp [m2, hpv, factor, of_apply, hrrow, hm1r])
  | inr hjEq =>
      have hjeq : j = pc := Fin.ext (by simpa using hjEq)
      subst hjeq
      have hzeror : m3 r j = 0 := by
        simpa [m3] using
          eliminateCol_pivotCol_zero
          (M := m2)
          (pivotRow := ⟨row, hrow⟩)
          (pivotCol := j)
          h1 r hrrow
      simpa using hzeror

private lemma step_pivot_one
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonState (M := M) row col bound pivs)
    (hrow : row < m) {pr : Fin m} {pc : Fin n}
    (hbound : bound ≤ pc.1) (hpr_ge : row ≤ pr.1) :
    let m1 := if pr.1 = row then M else swapRow M ⟨row, hrow⟩ pr
    let pivotVal : R := m1 ⟨row, hrow⟩ pc
    let m2 := if pivotVal = 1 then m1 else factor m1 ⟨row, hrow⟩ (pivotVal)⁻¹
    let m3 := eliminateColM m2 ⟨row, hrow⟩ pc
    (∀ j : Fin n, j < pc → m1 ⟨row, hrow⟩ j = 0) →
    (∀ j : Fin n, j < pc → m2 ⟨row, hrow⟩ j = 0) →
    (∀ j : Fin n, m3 ⟨row, hrow⟩ j = m2 ⟨row, hrow⟩ j) →
    m2 ⟨row, hrow⟩ pc = 1 →
    ∀ i : Fin m, ∀ hi : i.1 < row + 1, m3 i ((extendPivs row pivs pc) i hi) = 1 := by
  intro m1 pivotVal m2 m3 hzero_left_m1 hzero_left_m2 hrow_unchanged h1 i hi
  by_cases hlt : i.1 < row
  · have hp : M i (pivs i hlt) = 1 := hstate.pivot_one i hlt
    have hp_lt : pivs i hlt < pc :=
      pivot_lt_newPivot (M := M) row col bound pivs hstate (pc := pc) hbound i hlt
    simpa [extendPivs, hlt] using
      (calc
        m3 i (pivs i hlt) = m2 i (pivs i hlt) := by
          simpa [m3] using
            (eliminateCol_go_preserves_col (cur := m2) (pivotRow := ⟨row, hrow⟩)
              (pivotCol := pc) (r := 0) (steps := List.nil) (j := pivs i hlt)
              (hzero := hzero_left_m2 (pivs i hlt) hp_lt) i)
        _ = m1 i (pivs i hlt) := by
          by_cases hpv : pivotVal = 1
          · simp [m2, hpv]
          · have hne : i ≠ ⟨row, hrow⟩ := by
              intro hEq
              have : i.1 = row := by simpa using congrArg Fin.val hEq
              exact (lt_irrefl _ (this ▸ hlt))
            simp [m2, hpv, factor, of_apply, hne]
        _ = M i (pivs i hlt) := by
          by_cases hpr : pr.1 = row
          · simp [m1, hpr]
          · have hne1 : i ≠ ⟨row, hrow⟩ := by
              intro hEq
              have : i.1 = row := by simpa using congrArg Fin.val hEq
              exact (lt_irrefl _ (this ▸ hlt))
            have hne2 : i ≠ pr := by
              have hltpr : i.1 < pr.1 := by omega
              intro hEq
              have : i.1 = pr.1 := by simpa using congrArg Fin.val hEq
              exact (lt_irrefl _ (this ▸ hltpr))
            simp [m1, hpr, swapRow, of_apply, hne1, hne2]
        _ = 1 := hp)
  · have hi_eq : i.1 = row := by
      have hi_le : i.1 ≤ row := by omega
      exact le_antisymm hi_le (by omega)
    have hrowi : i = ⟨row, hrow⟩ := fin_eq_of_val_eq hrow hi_eq
    subst hrowi
    have hrowpc : m3 ⟨row, hrow⟩ pc = 1 := by
      have := hrow_unchanged pc
      simpa [h1] using this
    simp [extendPivs, hrowpc]

private lemma step_pivot_col_zero
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonState (M := M) row col bound pivs)
    (hrow : row < m) {pr : Fin m} {pc : Fin n}
    (hbound : bound ≤ pc.1) (hpr_ge : row ≤ pr.1) :
    let m1 := if pr.1 = row then M else swapRow M ⟨row, hrow⟩ pr
    let pivotVal : R := m1 ⟨row, hrow⟩ pc
    let m2 := if pivotVal = 1 then m1 else factor m1 ⟨row, hrow⟩ (pivotVal)⁻¹
    let m3 := eliminateColM m2 ⟨row, hrow⟩ pc
    (∀ j : Fin n, j < pc → m1 ⟨row, hrow⟩ j = 0) →
    (∀ j : Fin n, j < pc → m2 ⟨row, hrow⟩ j = 0) →
    m2 ⟨row, hrow⟩ pc = 1 →
    ∀ i : Fin m, ∀ hi : i.1 < row + 1, ∀ r : Fin m, r ≠ i →
      m3 r ((extendPivs row pivs pc) i hi) = 0 := by
  intro m1 pivotVal m2 m3 hzero_left_m1 hzero_left_m2 h1 i hi r hrne
  by_cases hlt : i.1 < row
  · have hp_lt : pivs i hlt < pc :=
      pivot_lt_newPivot (M := M) row col bound pivs hstate (pc := pc) hbound i hlt
    have hzeroM : M r (pivs i hlt) = 0 := hstate.pivot_col_zero i hlt r hrne
    have hzero_row_M : M ⟨row, hrow⟩ (pivs i hlt) = 0 := by
      have hne : (⟨row, hrow⟩ : Fin m) ≠ i := by
        intro hEq
        have : row = i.1 := by simpa using congrArg Fin.val hEq
        exact (lt_irrefl _ (this ▸ hlt))
      exact hstate.pivot_col_zero i hlt ⟨row, hrow⟩ hne
    have hzero_pr_M : M pr (pivs i hlt) = 0 := by
      have hne : pr ≠ i := by
        have hltpr : i.1 < pr.1 := by omega
        intro hEq
        have : pr.1 = i.1 := by simpa using congrArg Fin.val hEq
        exact (lt_irrefl _ (this ▸ hltpr))
      exact hstate.pivot_col_zero i hlt pr hne
    have hm1 : m1 r (pivs i hlt) = 0 := by
      by_cases hpr : pr.1 = row
      · simp [m1, hpr, hzeroM]
      · by_cases hrpr : r = pr
        · subst hrpr
          have hnerow : (r : Fin m) ≠ ⟨row, hrow⟩ := by
            intro hEq
            exact hpr (by simpa using congrArg Fin.val hEq)
          simp [m1, hpr, swapRow, of_apply, hnerow, hzero_row_M]
        · by_cases hrrow : r = ⟨row, hrow⟩
          · subst hrrow
            have hnepr : pr ≠ ⟨row, hrow⟩ := by
              intro hEq
              exact hpr (by simpa using congrArg Fin.val hEq)
            simp [m1, hpr, swapRow, of_apply, hzero_pr_M]
          · simp [m1, hpr, swapRow, of_apply, hrpr, hrrow, hzeroM]
    simpa [extendPivs, hlt] using
      (calc
        m3 r (pivs i hlt) = m2 r (pivs i hlt) := by
          simpa [m3] using
            (eliminateCol_go_preserves_col (cur := m2) (pivotRow := ⟨row, hrow⟩)
              (pivotCol := pc) (r := 0) (steps := List.nil) (j := pivs i hlt)
              (hzero := hzero_left_m2 (pivs i hlt) hp_lt) r)
        _ = 0 := by
          by_cases hpv : pivotVal = 1
          · simp [m2, hpv, hm1]
          · by_cases hrrow : r = ⟨row, hrow⟩
            · subst hrrow
              have h0 : m1 ⟨row, hrow⟩ (pivs i hlt) = 0 := hzero_left_m1 (pivs i hlt) hp_lt
              simp [m2, hpv, factor, of_apply, h0]
            · simp [m2, hpv, factor, of_apply, hrrow, hm1])
  · have hi_eq : i.1 = row := by
      have hi_le : i.1 ≤ row := by omega
      exact le_antisymm hi_le (by omega)
    have hrowi : i = ⟨row, hrow⟩ := fin_eq_of_val_eq hrow hi_eq
    subst hrowi
    have hzeror : m3 r pc = 0 := by
      simpa [m3] using
        eliminateCol_pivotCol_zero
        (M := m2)
        (pivotRow := ⟨row, hrow⟩)
        (pivotCol := pc)
        h1 r hrne
    simp [extendPivs, hzeror]

private lemma step_state
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonState (M := M) row col bound pivs)
    (hrow : row < m) (_hcol : col < n)
    {pr : Fin m} {pc : Fin n} (h : checkPivot M row col = some (pr, pc)) :
    let m1 := if pr.1 = row then M else swapRow M ⟨row, hrow⟩ pr
    let pivotVal : R := m1 ⟨row, hrow⟩ pc
    let m2 := if pivotVal = 1 then m1 else factor m1 ⟨row, hrow⟩ (pivotVal)⁻¹
    let m3 := eliminateColM m2 ⟨row, hrow⟩ pc
    EchelonState (M := m3) (row := row + 1) (col := col + 1) (bound := pc.1 + 1)
      (extendPivs row pivs pc) := by
  intro m1 pivotVal m2 m3
  -- basic bounds
  have hrowle : row ≤ m := Nat.le_of_lt hrow
  have hrow1 : row + 1 ≤ m := by omega
  have hbound : bound ≤ pc.1 := pivotCol_ge_bound (M := M) row col bound pivs hstate h
  have hcolle : col ≤ pc.1 := le_trans hstate.col_le hbound
  have hbound' : pc.1 + 1 ≤ n := by omega
  -- show pivotRow ≥ row
  have hpr_ge : row ≤ pr.1 := checkPivot_some_row_ge (M := M) row col h
  -- pivot row zeros left of pc in M
  have hzero_left : ∀ j : Fin n, j < pc → M pr j = 0 :=
    pivot_row_zero_left (M := M) row col bound pivs hstate h
  -- show pivot row zeros left of pc in m1
  have hzero_left_m1 : ∀ j : Fin n, j < pc → m1 ⟨row, hrow⟩ j = 0 := by
    intro j hj
    by_cases hpr : pr.1 = row
    · have : pr = ⟨row, hrow⟩ := by
        ext; exact hpr
      subst this
      simp [m1, hzero_left j hj]
    · have hne : ⟨row, hrow⟩ ≠ pr := by
        intro hEq
        exact hpr (by simpa [eq_comm] using congrArg Fin.val hEq)
      -- swapRow brings pr to row
      have : m1 ⟨row, hrow⟩ j = M pr j := by
        simp [m1, hpr, swapRow, of_apply]
      simpa [this] using hzero_left j hj
  -- show pivot entry nonzero in m1
  have hneq : m1 ⟨row, hrow⟩ pc ≠ 0 := by
    by_cases hpr : pr.1 = row
    · have : pr = ⟨row, hrow⟩ := by
        ext; exact hpr
      subst this
      simpa [m1, hpr] using checkPivot_some_nonzero (M := M) row col h
    · have hne : ⟨row, hrow⟩ ≠ pr := by
        intro hEq
        exact hpr (by simpa [eq_comm] using congrArg Fin.val hEq)
      -- swapRow moves pr to row
      have : m1 ⟨row, hrow⟩ pc = M pr pc := by
        simp [m1, hpr, swapRow, of_apply]
      simpa [this] using checkPivot_some_nonzero (M := M) row col h
  -- pivot entry is 1 in m2
  have h1 : m2 ⟨row, hrow⟩ pc = 1 := by
    by_cases hpv : pivotVal = 1
    · simp [m2, hpv, pivotVal]
    · -- factor by pivotVal⁻¹
      simp [m2, hpv, pivotVal, factor, of_apply, hneq]
  -- pivot row unchanged by eliminateColM
  have hrow_unchanged : ∀ j : Fin n, m3 ⟨row, hrow⟩ j = m2 ⟨row, hrow⟩ j := by
    intro j
    -- eliminateColM skips pivotRow
    simpa [m3] using eliminateCol_pivotRow (M := m2) (pivotRow := ⟨row, hrow⟩) (pivotCol := pc) j
  -- pivot row zeros left of pc in m2
  have hzero_left_m2 : ∀ j : Fin n, j < pc → m2 ⟨row, hrow⟩ j = 0 := by
    intro j hj
    by_cases hpv : pivotVal = 1
    · simp [m2, hpv, hzero_left_m1 j hj]
    · -- factor does not change zeros
      simp [m2, hpv, factor, of_apply, hzero_left_m1 j hj]
  -- build new state
  refine mkEchelonState (M := m3) (row := row + 1) (col := col + 1) (bound := pc.1 + 1)
    (pivs := extendPivs row pivs pc)
    ?row_le
    ?bound_le
    ?col_le
    ?pivot_row
    ?pivot_strict
    ?pivot_lt_bound
    ?cols_zero
    ?pivot_one
    ?pivot_col_zero
  · exact hrow1
  · exact hbound'
  · exact Nat.succ_le_succ hcolle
  · simpa [m1, pivotVal, m2, m3] using
      (step_pivot_row (M := M) row col bound pivs hstate hrow
        (pr := pr) (pc := pc) hbound hpr_ge
        hzero_left_m2 hrow_unchanged h1)
  · exact
      step_pivot_strict (M := M) row col bound pivs hstate (pc := pc) hbound
  · exact
      step_pivot_lt_bound (M := M) row col bound pivs hstate (pc := pc) hbound
  · simpa [m1, pivotVal, m2, m3] using
      (step_cols_lt_bound_zero (M := M) row col bound pivs hstate hrow
        (pr := pr) (pc := pc) h hbound
        hzero_left_m2 h1)
  · simpa [m1, pivotVal, m2, m3] using
      (step_pivot_one (M := M) row col bound pivs hstate hrow
        (pr := pr) (pc := pc) hbound hpr_ge
        hzero_left_m1 hzero_left_m2 hrow_unchanged h1)
  · simpa [m1, pivotVal, m2, m3] using
      (step_pivot_col_zero (M := M) row col bound pivs hstate hrow
        (pr := pr) (pc := pc) hbound hpr_ge
        hzero_left_m1 hzero_left_m2 h1)

/-! Main theorem. -/

private lemma rrefAux_isReducedEchelon
    (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
    (steps : List (RowOp m R))
    (pivs : ∀ i : Fin m, i.1 < row → Fin n)
    (hstate : EchelonState (M := M) row col bound pivs) :
    IsReducedEchelonForm (M := rrefAuxM M row col steps) := by
  -- induction on remaining rows
  have hrec :
      ∀ k (M : Matrix (Fin m) (Fin n) R) (row col bound : Nat)
        (steps : List (RowOp m R)) (pivs : ∀ i : Fin m, i.1 < row → Fin n),
        m - row = k →
        EchelonState (M := M) row col bound pivs →
        IsReducedEchelonForm (M := rrefAuxM M row col steps) := by
    intro k
    refine Nat.strongRecOn k ?_
    intro k ih M row col bound steps pivs hk hstate
    by_cases hrow : row < m
    · by_cases hcol : col < n
      · -- unfold rrefAuxM one step and analyze checkPivot
        rw [rrefAuxM, rrefAux.eq_1]
        simp only [hrow, hcol]
        cases hcp : checkPivot M row col with
        | none =>
            -- no pivot: remaining submatrix is zero
            have hnone : checkPivot M row col = none := hcp
            have hzero : ∀ r : Fin m, row ≤ r.1 → RowIsZero M r :=
              zero_rows_of_checkPivot_none (M := M) row col bound pivs hstate hnone
            exact reduced_of_state (M := M) row col bound pivs
              hstate.toEchelonStateCore hstate.toReducedStateExtras hzero
        | some prpc =>
            cases prpc with
            | mk pr pc =>
                -- build step state and recurse
                have hstate' := step_state (M := M) row col bound pivs hstate hrow hcol hcp
                -- compute new matrix
                let m1 := if pr.1 = row then M else swapRow M ⟨row, hrow⟩ pr
                let pivotVal : R := m1 ⟨row, hrow⟩ pc
                let m2 := if pivotVal = 1 then m1 else factor m1 ⟨row, hrow⟩ (pivotVal)⁻¹
                let m3 := eliminateColM m2 ⟨row, hrow⟩ pc
                let steps' :=
                  steps ++
                    [RowOp.swap ⟨row, hrow⟩ pr,
                      RowOp.factor ⟨row, hrow⟩ (pivotVal)⁻¹]
                have hklt : m - (row + 1) < k := by
                  have hlt : m - (row + 1) < m - row := by omega
                  simpa [hk] using hlt
                have helim :
                    (eliminateCol m2 ⟨row, hrow⟩ pc steps' true).1 = m3 := by
                  simpa [m3, steps'] using
                    (eliminateCol_matrix_irrel
                      (M := m2)
                      (pivotRow := ⟨row, hrow⟩)
                      (pivotCol := pc)
                      (steps := steps'))
                simpa [m1, pivotVal, m2, m3, steps', helim] using
                  ih (m - (row + 1)) hklt
                    m3 (row + 1) (col + 1) (pc.1 + 1)
                    ((eliminateCol m2 ⟨row, hrow⟩ pc steps' true).2)
                    (extendPivs row pivs pc) rfl hstate'
      · -- col ≥ n, so rrefAuxM returns M
        have hcol' : ¬ col < n := hcol
        rw [rrefAuxM, rrefAux.eq_1]
        simp only [hrow, hcol']
        have hzero : ∀ r : Fin m, row ≤ r.1 → RowIsZero M r :=
          zero_rows_of_col_ge (M := M) row col bound pivs hstate hcol'
        exact reduced_of_state (M := M) row col bound pivs
          hstate.toEchelonStateCore hstate.toReducedStateExtras hzero
    · -- row ≥ m
      have hrow' : ¬ row < m := hrow
      rw [rrefAuxM, rrefAux.eq_1]
      simp only [hrow']
      have hzero : ∀ r : Fin m, row ≤ r.1 → RowIsZero M r :=
        zero_rows_of_row_ge (M := M) row (by omega)
      exact reduced_of_state (M := M) row col bound pivs
        hstate.toEchelonStateCore hstate.toReducedStateExtras hzero
  exact hrec (m - row) M row col bound steps pivs rfl hstate

/-! Final theorem. -/

theorem rowReducedEchelonForm_isReducedEchelon
    (M : Matrix (Fin m) (Fin n) R) :
    IsReducedEchelonForm (M := (rowReducedEchelonForm M).1) := by
  classical
  have hstate : EchelonState (M := M) (row := 0) (col := 0) (bound := 0) emptyPivs :=
    initial_state (M := M)
  simpa [rowReducedEchelonForm] using
    (rrefAux_isReducedEchelon (M := M) (row := 0) (col := 0) (bound := 0)
      (steps := List.nil) (pivs := emptyPivs)
      (hstate := hstate))

/-- Compatibility theorem: derive REF directly from the stronger RREF result. -/
theorem rowReducedEchelonForm_isEchelon
    (M : Matrix (Fin m) (Fin n) R) :
    IsEchelonForm (M := (rowReducedEchelonForm M).1) :=
  (rowReducedEchelonForm_isReducedEchelon (M := M)).echelon

end Matrix
