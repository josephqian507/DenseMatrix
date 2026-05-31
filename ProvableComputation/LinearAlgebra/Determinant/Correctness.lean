/-
Copyright (c) 2026 Provable Computation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Provable Computation contributors
-/

import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import ProvableComputation.LinearAlgebra.Determinant.Basic
import ProvableComputation.LinearAlgebra.LU.Correctness

/-!
# Determinant Correctness Building Blocks

This module proves the determinant effects of the row operations used by the
executable elimination code, connects echelon diagonal products to mathlib's
determinant, derives determinant relations from verified LU reconstruction,
and proves that the public `Matrix.gaussDet` and `Matrix.luDet` wrappers equal
`Matrix.det` on square matrices over fields.
-/

open Matrix

namespace DeterminantInternal

variable {R : Type} [Field R]
variable {n : Nat}

/-
The first group ties the executable row operations to determinant algebra.
`rawLuDet` consumes only a step log and an echelon matrix, so each constructor of
`RowOp` needs a precise determinant multiplier before the higher-level proof can
talk about whole elimination traces.
-/
omit [Field R] in
theorem swapRow_eq_submatrix (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    swapRow M i j = M.submatrix (Equiv.swap i j) id := by
  ext r c
  simp only [swapRow, Matrix.of_apply, Matrix.submatrix_apply, id_eq]
  rw [Equiv.swap_apply_def]
  split_ifs <;> simp_all

omit [Field R] in
theorem swapRow_self (M : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    swapRow M i i = M := by
  ext r c
  by_cases h : r = i
  · simp [swapRow, h]
  · simp [swapRow, h]

theorem det_swapRow (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (swapRow M i j).det = (if i = j then 1 else -1) * M.det := by
  by_cases hij : i = j
  · subst hij
    simp [swapRow_self]
  · rw [swapRow_eq_submatrix]
    rw [Matrix.det_permute]
    rw [Equiv.Perm.sign_swap hij]
    simp [hij]

theorem factor_eq_updateRow (M : Matrix (Fin n) (Fin n) R) (i : Fin n) (c : R) :
    factor M i c = M.updateRow i (c • M i) := by
  ext r s
  by_cases h : r = i
  · subst h
    simp [factor]
  · simp [factor, h]

theorem det_factor (M : Matrix (Fin n) (Fin n) R) (i : Fin n) (c : R) :
    (factor M i c).det = c * M.det := by
  rw [factor_eq_updateRow]
  simpa using Matrix.det_updateRow_smul (M := M) (j := i) (s := c) (u := M i)

theorem replace_eq_updateRow (M : Matrix (Fin n) (Fin n) R)
    {use toReplace : Fin n} (k : R) (huse : use ≠ toReplace) :
    replace M use toReplace k = M.updateRow toReplace (M toReplace + k • M use) := by
  ext i j
  by_cases hi : i = toReplace
  · subst hi
    simp [replace, huse]
  · simp [replace, huse, hi]

theorem det_replace (M : Matrix (Fin n) (Fin n) R)
    (use toReplace : Fin n) (k : R) :
    (replace M use toReplace k).det =
      (if use = toReplace then k + 1 else 1) * M.det := by
  by_cases huse : use = toReplace
  · subst huse
    simp [replace, det_factor]
  · rw [replace_eq_updateRow M k huse]
    have hdet := Matrix.det_updateRow_add_smul_self
      (A := M) (i := toReplace) (j := use) (Ne.symm huse) k
    simpa [huse] using hdet

theorem det_applyRowOp (M : Matrix (Fin n) (Fin n) R) (op : RowOp n R) :
    (Matrix.applyRowOp M op).det = rowOpDetMultiplier op * M.det := by
  cases op with
  | swap i j =>
      simpa [Matrix.applyRowOp, rowOpDetMultiplier] using
        det_swapRow (M := M) i j
  | factor i c =>
      simpa [Matrix.applyRowOp, rowOpDetMultiplier] using
        det_factor (M := M) i c
  | replace use toReplace k =>
      simpa [Matrix.applyRowOp, rowOpDetMultiplier] using
        det_replace (M := M) use toReplace k

theorem det_foldl_applyRowOp (M : Matrix (Fin n) (Fin n) R) (steps : List (RowOp n R)) :
    (steps.foldl Matrix.applyRowOp M).det = detMultiplierOfSteps steps * M.det := by
  induction steps generalizing M with
  | nil => simp [detMultiplierOfSteps]
  | cons op ops ih =>
      simp only [List.foldl_cons]
      rw [ih (M := Matrix.applyRowOp M op)]
      rw [det_applyRowOp]
      simp [detMultiplierOfSteps]
      ring

theorem det_eq_diagonalProduct_of_upperTriangular
    (M : squareMatrix n R) (hM : M.BlockTriangular id) :
    M.det = diagonalProduct M := by
  simpa [diagonalProduct] using Matrix.det_of_upperTriangular (M := M) hM

theorem det_eq_one_of_isUnitLowerTriangular
    (L : squareMatrix n R) (hL : IsUnitLowerTriangular L) :
    L.det = 1 := by
  rw [Matrix.det_of_lowerTriangular L hL.1]
  simp [hL.2]

theorem diagonalProduct_eq_one_of_isUnitLowerTriangular
    (L : squareMatrix n R) (hL : IsUnitLowerTriangular L) :
    diagonalProduct L = 1 := by
  simp [diagonalProduct, hL.2]

/-
For square matrices, the repository's echelon predicate is strong enough to
force upper triangularity.  This bridge is what lets determinant correctness use
mathlib's triangular determinant theorem after running the executable Gaussian
elimination code.
-/
theorem pivot_col_ge_row_of_isEchelonForm
    {M : Matrix (Fin n) (Fin n) R} (h : IsEchelonForm (M := M))
    {i p : Fin n} (hp : IsPivot M i p) :
    i.1 ≤ p.1 := by
  classical
  have hmain :
      ∀ k (i : Fin n) (p : Fin n), i.1 = k → IsPivot M i p → k ≤ p.1 := by
    intro k
    induction k with
    | zero =>
        intro i p hi hp
        omega
    | succ k ih =>
        intro i p hi hp
        have hklt : k < n := by omega
        let prev : Fin n := ⟨k, hklt⟩
        have hprev_lt : prev < i := by
          rw [Fin.lt_def]
          dsimp [prev]
          omega
        rcases h.row_zero_or_pivot prev with hzero | hprevpivot
        · have hizero : RowIsZero M i := h.zero_rows_bottom prev i hprev_lt hzero
          exact False.elim (RowIsZero.not_isPivot (M := M) (i := i) (p := p) hizero hp)
        · rcases hprevpivot with ⟨q, hq⟩
          have hq_lt_p : q < p := h.pivots_strictly_increasing prev i q p hprev_lt hq hp
          have hk_le_q : k ≤ q.1 := ih prev q rfl hq
          rw [Fin.lt_def] at hq_lt_p
          omega
  exact hmain i.1 i p rfl hp

theorem blockTriangular_of_isEchelonForm
    (M : squareMatrix n R) (h : IsEchelonForm (M := M)) :
    M.BlockTriangular id := by
  intro i j hji
  change j < i at hji
  rcases h.row_zero_or_pivot i with hzero | hpiv
  · exact hzero j
  · rcases hpiv with ⟨p, hp⟩
    have hi_le_p : i.1 ≤ p.1 := pivot_col_ge_row_of_isEchelonForm (h := h) hp
    have hj_lt_i : j.1 < i.1 := hji
    have hj_lt_p_val : j.1 < p.1 := lt_of_lt_of_le hj_lt_i hi_le_p
    have hj_lt_p : j < p := by
      rw [Fin.lt_def]
      exact hj_lt_p_val
    exact hp.2 j hj_lt_p

/-
The REF path used by `luDet` records swaps and row replacements but does not
record row scaling.  Its determinant multipliers are therefore involutive:
swaps square to one and replacements contribute one.  The product-level lemma
packages that invariant for the final determinant calculation.
-/
theorem detMultiplierOfSteps_mul_self
    (steps : List (RowOp n R))
    (hsteps : ∀ op ∈ steps, rowOpDetMultiplier op * rowOpDetMultiplier op = 1) :
    detMultiplierOfSteps steps * detMultiplierOfSteps steps = 1 := by
  induction steps with
  | nil =>
      simp [detMultiplierOfSteps]
  | cons op ops ih =>
      have hop : rowOpDetMultiplier op * rowOpDetMultiplier op = 1 := hsteps op (by simp)
      have hops : ∀ op' ∈ ops, rowOpDetMultiplier op' * rowOpDetMultiplier op' = 1 := by
        intro op' hop'
        exact hsteps op' (by simp [hop'])
      have ihops := ih hops
      have ihprod :
          (ops.map rowOpDetMultiplier).prod * (ops.map rowOpDetMultiplier).prod = 1 := by
        simpa [detMultiplierOfSteps] using ihops
      simp only [detMultiplierOfSteps, List.map_cons, List.prod_cons]
      calc
        (rowOpDetMultiplier op * (ops.map rowOpDetMultiplier).prod) *
            (rowOpDetMultiplier op * (ops.map rowOpDetMultiplier).prod)
            =
              (rowOpDetMultiplier op * rowOpDetMultiplier op) *
                ((ops.map rowOpDetMultiplier).prod *
                  (ops.map rowOpDetMultiplier).prod) := by
                ring
        _ = 1 := by simp [hop, ihprod]

section RowEchelonLog

variable [DecidableEq R]

/-
The following log invariants follow the same recursion shape as `Rref.lean`.
They prove that every operation appended by the non-reduced REF algorithm has an
involutive determinant multiplier, even after nested elimination loops extend
the existing step list.
-/
theorem eliminateColLoop_steps_detMultiplier_mul_self
    (pivotRow pivotCol : Fin n) (r : Nat)
    (M : Matrix (Fin n) (Fin n) R) (steps : List (RowOp n R))
    (hsteps : ∀ op ∈ steps, rowOpDetMultiplier op * rowOpDetMultiplier op = 1) :
    ∀ op ∈ (GaussianEliminationInternal.eliminateColLoop pivotRow pivotCol r M steps).2,
      rowOpDetMultiplier op * rowOpDetMultiplier op = 1 := by
  have hrec :
      ∀ k (r : Nat) (M : Matrix (Fin n) (Fin n) R) (steps : List (RowOp n R)),
        n - r = k →
        (∀ op ∈ steps, rowOpDetMultiplier op * rowOpDetMultiplier op = 1) →
        ∀ op ∈ (GaussianEliminationInternal.eliminateColLoop pivotRow pivotCol r M steps).2,
          rowOpDetMultiplier op * rowOpDetMultiplier op = 1 := by
    intro k
    induction k with
    | zero =>
        intro r M steps hk hsteps op hop
        have hr : n ≤ r := Nat.le_of_sub_eq_zero hk
        rw [GaussianEliminationInternal.eliminateColLoop,
          GaussianEliminationInternal.eliminateColLoopAux,
          dif_neg (not_lt_of_ge hr)] at hop
        exact hsteps op hop
    | succ k ih =>
        intro r M steps hk hsteps op hop
        have hr : r < n := by omega
        have hk' : n - (r + 1) = k := by omega
        let i : Fin n := ⟨r, hr⟩
        rw [GaussianEliminationInternal.eliminateColLoop,
          GaussianEliminationInternal.eliminateColLoopAux, dif_pos hr] at hop
        by_cases hEq : i = pivotRow
        · exact ih (r + 1) M steps hk' hsteps op
            (by simpa [i, hEq, dite_eq_ite] using hop)
        · by_cases hcoeff : M i pivotCol ≠ 0
          · let op' : RowOp n R := .replace pivotRow i (-M i pivotCol / M pivotRow pivotCol)
            let M' := replace M pivotRow i (-M i pivotCol / M pivotRow pivotCol)
            let steps' := steps ++ [op']
            have hsteps' :
                ∀ op ∈ steps', rowOpDetMultiplier op * rowOpDetMultiplier op = 1 := by
              intro op'' hop''
              have hop'' : op'' ∈ steps ∨ op'' = op' := by
                simpa [steps', List.mem_append, List.mem_singleton] using hop''
              rcases hop'' with hop'' | rfl
              · exact hsteps op'' hop''
              · have huse : pivotRow ≠ i := by
                  intro hpr
                  exact hEq hpr.symm
                simp [op', rowOpDetMultiplier, huse]
            have huse : pivotRow ≠ i := by
              intro hpr
              exact hEq hpr.symm
            have hpivot' : M' pivotRow pivotCol = M pivotRow pivotCol := by
              simp [M', replace, huse]
            have hop' :
                op ∈ (GaussianEliminationInternal.eliminateColLoop pivotRow pivotCol
                  (r + 1) M' steps').2 := by
              change op ∈ (GaussianEliminationInternal.eliminateColLoopAux pivotRow pivotCol
                (M' pivotRow pivotCol) (r + 1) M' steps').2
              simpa [hpivot', i, hEq, hcoeff, op', M', steps', List.concat_eq_append,
                dite_eq_ite] using hop
            exact ih (r + 1) M' steps' hk' hsteps' op hop'
          · exact ih (r + 1) M steps hk' hsteps op
              (by simpa [i, hEq, hcoeff, dite_eq_ite] using hop)
  exact hrec (n - r) r M steps rfl hsteps

theorem eliminateColCore_steps_detMultiplier_mul_self
    (M : Matrix (Fin n) (Fin n) R) (pivotRow pivotCol : Fin n)
    (steps : List (RowOp n R)) (reduced : Bool)
    (hsteps : ∀ op ∈ steps, rowOpDetMultiplier op * rowOpDetMultiplier op = 1) :
    ∀ op ∈ (GaussianEliminationInternal.eliminateColCore M pivotRow pivotCol steps reduced).2,
      rowOpDetMultiplier op * rowOpDetMultiplier op = 1 := by
  rw [GaussianEliminationInternal.eliminateColCore]
  by_cases hred : reduced
  · simpa [hred] using
      eliminateColLoop_steps_detMultiplier_mul_self
        (R := R) (pivotRow := pivotRow) (pivotCol := pivotCol) (r := 0)
        (M := M) (steps := steps) hsteps
  · simpa [hred] using
      eliminateColLoop_steps_detMultiplier_mul_self
        (R := R) (pivotRow := pivotRow) (pivotCol := pivotCol) (r := pivotRow.1)
        (M := M) (steps := steps) hsteps

theorem rowReductionAux_false_steps_detMultiplier_mul_self
    (M : Matrix (Fin n) (Fin n) R) (r c : Nat) (steps : List (RowOp n R))
    (hsteps : ∀ op ∈ steps, rowOpDetMultiplier op * rowOpDetMultiplier op = 1) :
    ∀ op ∈ (GaussianEliminationInternal.rowReductionAux M r c steps false).2,
      rowOpDetMultiplier op * rowOpDetMultiplier op = 1 := by
  have hrec :
      ∀ k (M : Matrix (Fin n) (Fin n) R) (r c : Nat) (steps : List (RowOp n R)),
        n - r = k →
        (∀ op ∈ steps, rowOpDetMultiplier op * rowOpDetMultiplier op = 1) →
        ∀ op ∈ (GaussianEliminationInternal.rowReductionAux M r c steps false).2,
          rowOpDetMultiplier op * rowOpDetMultiplier op = 1 := by
    intro k
    induction k with
    | zero =>
        intro M r c steps hk hsteps op hop
        have hr : n ≤ r := Nat.le_of_sub_eq_zero hk
        have hop' : op ∈ steps := by
          simpa [GaussianEliminationInternal.rowReductionAux, Nat.not_lt_of_ge hr] using hop
        exact hsteps op hop'
    | succ k ih =>
        intro M r c steps hk hsteps op hop
        have hr : r < n := by omega
        have hk' : n - (r + 1) = k := by omega
        rw [GaussianEliminationInternal.rowReductionAux, dif_pos hr] at hop
        by_cases hc : c < n
        · rw [if_pos hc] at hop
          cases hcp : checkPivot M r c with
          | none =>
              have hop' : op ∈ steps := by
                simpa [hcp] using hop
              exact hsteps op hop'
          | some p =>
              rcases p with ⟨pivotRow, pivotCol⟩
              let rowFin : Fin n := ⟨r, hr⟩
              let swapOp : RowOp n R := .swap rowFin pivotRow
              let steps1 : List (RowOp n R) := steps ++ [swapOp]
              let m1 : Matrix (Fin n) (Fin n) R :=
                if pivotRow.1 = r then M else swapRow M rowFin pivotRow
              have hsteps1 :
                  ∀ op ∈ steps1, rowOpDetMultiplier op * rowOpDetMultiplier op = 1 := by
                intro op' hop'
                have hop' : op' ∈ steps ∨ op' = swapOp := by
                  simpa [steps1, List.mem_append, List.mem_singleton] using hop'
                rcases hop' with hop' | rfl
                · exact hsteps op' hop'
                · by_cases hswap : rowFin = pivotRow
                  · simp [swapOp, rowOpDetMultiplier, hswap]
                  · simp [swapOp, rowOpDetMultiplier, hswap]
              let res :=
                GaussianEliminationInternal.eliminateColCore m1 rowFin pivotCol steps1 false
              have hres :
                  ∀ op ∈ res.2, rowOpDetMultiplier op * rowOpDetMultiplier op = 1 := by
                simpa [res] using
                  eliminateColCore_steps_detMultiplier_mul_self
                    (R := R) (M := m1) (pivotRow := rowFin) (pivotCol := pivotCol)
                    (steps := steps1) (reduced := false) hsteps1
              exact ih res.1 (r + 1) (c + 1) res.2 hk' hres op
                (by simpa [hcp, rowFin, steps1, m1, res, List.concat_eq_append] using hop)
        · have hop' : op ∈ steps := by
            simpa [hc] using hop
          exact hsteps op hop'
  exact hrec (n - r) M r c steps rfl hsteps

theorem rawRowEchelonForm_steps_detMultiplier_mul_self
    (M : Matrix (Fin n) (Fin n) R) :
    ∀ op ∈ (GaussianEliminationInternal.rawRowEchelonForm M).2,
      rowOpDetMultiplier op * rowOpDetMultiplier op = 1 := by
  simpa [GaussianEliminationInternal.rawRowEchelonForm] using
    rowReductionAux_false_steps_detMultiplier_mul_self
      (R := R) (M := M) (r := 0) (c := 0) (steps := []) (by simp)

end RowEchelonLog

section LU

variable [DecidableEq R]

/-
The LU determinant facts are derived from the already-proved reconstruction
theorem `P * L * U = M`.  The lower factor is unit triangular, so its determinant
drops out and the only remaining runtime data is the permutation determinant and
the diagonal product of the echelon factor.
-/
theorem rawFactorization_det_relation (M : squareMatrix n R) :
    let raw := LUFactorizationInternal.rawFactorization (R := R) M
    raw.1.det * raw.2.1.det * raw.2.2.det = M.det := by
  dsimp only
  have h := LUFactorizationInternal.rawFactorization_reconstruct (R := R) (M := M)
  have hdet := congrArg Matrix.det h
  simpa [Matrix.det_mul, mul_assoc] using hdet

theorem rawFactorization_det_relation_without_lower (M : squareMatrix n R) :
    let raw := LUFactorizationInternal.rawFactorization (R := R) M
    raw.1.det * raw.2.2.det = M.det := by
  dsimp only
  have hdet := rawFactorization_det_relation (R := R) (M := M)
  have hLdet :
      (LUFactorizationInternal.rawFactorization (R := R) M).2.1.det = 1 := by
    exact det_eq_one_of_isUnitLowerTriangular
      (L := (LUFactorizationInternal.rawFactorization (R := R) M).2.1)
      (LUFactorizationInternal.rawFactorization_lower_isUnitLowerTriangular (R := R) (M := M))
  simpa [hLdet, mul_assoc] using hdet

theorem rawFactorization_upper_det_eq_diagonalProduct
    (M : squareMatrix n R)
    (hU : (LUFactorizationInternal.rawFactorization (R := R) M).2.2.BlockTriangular id) :
    (LUFactorizationInternal.rawFactorization (R := R) M).2.2.det =
      diagonalProduct (LUFactorizationInternal.rawFactorization (R := R) M).2.2 := by
  exact det_eq_diagonalProduct_of_upperTriangular
    (M := (LUFactorizationInternal.rawFactorization (R := R) M).2.2) hU

theorem rawFactorization_det_eq_permutation_det_mul_diagonalProduct
    (M : squareMatrix n R)
    (hU : (LUFactorizationInternal.rawFactorization (R := R) M).2.2.BlockTriangular id) :
    (LUFactorizationInternal.rawFactorization (R := R) M).1.det *
      diagonalProduct (LUFactorizationInternal.rawFactorization (R := R) M).2.2 =
        M.det := by
  have hdet := rawFactorization_det_relation_without_lower (R := R) (M := M)
  have hUdet := rawFactorization_upper_det_eq_diagonalProduct (R := R) (M := M) hU
  simpa [hUdet] using hdet

theorem rawGaussDet_eq_det (M : squareMatrix n R) :
    DeterminantInternal.rawGaussDet M = M.det := by
  -- The proof compares the runtime determinant formula with the determinant of
  -- the logged REF result. The same multiplier appears once in the runtime
  -- formula and once in the determinant effect of the row-operation fold.
  let raw := GaussianEliminationInternal.rawRowEchelonForm M
  let U : squareMatrix n R := raw.1
  let steps : List (RowOp n R) := raw.2
  let mult : R := DeterminantInternal.detMultiplierOfSteps steps
  have hsteps :
      steps.foldl Matrix.applyRowOp M = U := by
    simpa [Matrix.rowEchelonForm, raw, U, steps] using
      Matrix.rowEchelonForm_steps (M := M)
  have hdet_fold :
      U.det = mult * M.det := by
    have h :=
      DeterminantInternal.det_foldl_applyRowOp (M := M) (steps := steps)
    simpa [hsteps, mult] using h
  have hU_echelon : IsEchelonForm (M := U) := by
    simpa [Matrix.rowEchelonForm, raw, U] using
      Matrix.rowEchelonForm_isEchelonForm (M := M)
  have hU_tri : U.BlockTriangular id :=
    DeterminantInternal.blockTriangular_of_isEchelonForm (M := U) hU_echelon
  have hU_diag : U.det = DeterminantInternal.diagonalProduct U :=
    DeterminantInternal.det_eq_diagonalProduct_of_upperTriangular (M := U) hU_tri
  have hmult_self : mult * mult = 1 := by
    exact DeterminantInternal.detMultiplierOfSteps_mul_self (R := R) (steps := steps)
      (by
        intro op hop
        exact DeterminantInternal.rawRowEchelonForm_steps_detMultiplier_mul_self
          (R := R) (M := M) op (by simpa [raw, steps] using hop))
  calc
    DeterminantInternal.rawGaussDet M = mult * DeterminantInternal.diagonalProduct U := by
      simp [DeterminantInternal.rawGaussDet, raw, U, steps, mult]
    _ = mult * U.det := by rw [← hU_diag]
    _ = mult * (mult * M.det) := by rw [hdet_fold]
    _ = (mult * mult) * M.det := by ring
    _ = M.det := by simp [hmult_self]

theorem rawLuDet_eq_rawGaussDet (M : squareMatrix n R) :
    DeterminantInternal.rawLuDet M = DeterminantInternal.rawGaussDet M := by
  rcases hraw : GaussianEliminationInternal.rawRowEchelonForm M with ⟨U, steps⟩
  have hLunit :
      IsUnitLowerTriangular
        ((LUFactorizationInternal.buildPLFromSteps (R := R) steps).2) := by
    have h :=
      LUFactorizationInternal.rawFactorization_lower_isUnitLowerTriangular
        (R := R) (M := M)
    simpa [LUFactorizationInternal.rawFactorization, hraw] using h
  have hLdiag :
      DeterminantInternal.diagonalProduct
        ((LUFactorizationInternal.buildPLFromSteps (R := R) steps).2) = 1 :=
    DeterminantInternal.diagonalProduct_eq_one_of_isUnitLowerTriangular
      (R := R)
      (L := (LUFactorizationInternal.buildPLFromSteps (R := R) steps).2)
      hLunit
  simp [DeterminantInternal.rawLuDet, DeterminantInternal.rawGaussDet,
    LUFactorizationInternal.rawFactorizationWithSteps, hraw, hLdiag]

end LU

end DeterminantInternal

namespace Matrix

variable {R : Type} [Field R] [DecidableEq R]
variable {n : Nat}

/-
The public Matrix API now routes executable work through DenseMatrix, but the
correctness statements normalize back to the internal Matrix algorithms.  These
wrappers keep the theorem surface stable while allowing the runtime backend to
change underneath it.
-/
theorem luFactorization_det_relation (M : squareMatrix n R) :
    let lu := Matrix.luFactorization M
    lu.P.det * lu.L.det * lu.U.det = M.det := by
  simpa [Matrix.luFactorization] using
    DeterminantInternal.rawFactorization_det_relation (R := R) (M := M)

theorem luFactorization_det_relation_without_lower (M : squareMatrix n R) :
    let lu := Matrix.luFactorization M
    lu.P.det * lu.U.det = M.det := by
  simpa [Matrix.luFactorization] using
    DeterminantInternal.rawFactorization_det_relation_without_lower (R := R) (M := M)

theorem luFactorization_det_eq_permutation_det_mul_diagonalProduct
    (M : squareMatrix n R)
    (hU : (Matrix.luFactorization M).U.BlockTriangular id) :
    (Matrix.luFactorization M).P.det *
      Matrix.diagonalProduct (Matrix.luFactorization M).U = M.det := by
  have hUraw : (LUFactorizationInternal.rawFactorization (R := R) M).2.2.BlockTriangular id := by
    simpa [Matrix.luFactorization] using hU
  simpa [Matrix.luFactorization, Matrix.diagonalProduct] using
    DeterminantInternal.rawFactorization_det_eq_permutation_det_mul_diagonalProduct
      (R := R) (M := M) hUraw

theorem luFactorization_upper_blockTriangular (M : squareMatrix n R) :
    (Matrix.luFactorization M).U.BlockTriangular id :=
  DeterminantInternal.blockTriangular_of_isEchelonForm
    (M := (Matrix.luFactorization M).U)
    (Matrix.luFactorization_upper_isEchelonForm (R := R) (M := M))

theorem luDet_eq_det (M : squareMatrix n R) :
    Matrix.luDet M = M.det := by
  calc
    Matrix.luDet M = DeterminantInternal.rawLuDet M := by
      simp [Matrix.luDet]
    _ = DeterminantInternal.rawGaussDet M :=
      DeterminantInternal.rawLuDet_eq_rawGaussDet (R := R) (M := M)
    _ = M.det :=
      DeterminantInternal.rawGaussDet_eq_det (R := R) (M := M)

theorem gaussDet_eq_det (M : squareMatrix n R) :
    Matrix.gaussDet M = M.det := by
  calc
    Matrix.gaussDet M = DeterminantInternal.rawGaussDet M := by
      simp [Matrix.gaussDet]
    _ = M.det :=
      DeterminantInternal.rawGaussDet_eq_det (R := R) (M := M)

end Matrix

namespace DenseMatrix

variable {R : Type} [Field R] [DecidableEq R]
variable {n : Nat}

/-
DenseMatrix determinant correctness is transported through `toMatrix`.  The
dense algorithms are executable over row-major storage, while `Matrix.det`
remains the mathematical specification used throughout the existing proof stack.
-/
theorem luFactorization_det_relation (M : DenseMatrix n n R) :
    let lu := DenseMatrix.luFactorization (R := R) M
    lu.P.toMatrix.det * lu.L.toMatrix.det * lu.U.toMatrix.det = M.toMatrix.det := by
  simpa using
    DeterminantInternal.rawFactorization_det_relation (R := R) (M := M.toMatrix)

theorem luFactorization_det_relation_without_lower (M : DenseMatrix n n R) :
    let lu := DenseMatrix.luFactorization (R := R) M
    lu.P.toMatrix.det * lu.U.toMatrix.det = M.toMatrix.det := by
  simpa using
    DeterminantInternal.rawFactorization_det_relation_without_lower (R := R) (M := M.toMatrix)

theorem luDet_eq_det (M : DenseMatrix n n R) :
    DenseMatrix.luDet M = M.toMatrix.det := by
  simpa [Matrix.luDet] using
    Matrix.luDet_eq_det (R := R) (M := M.toMatrix)

theorem gaussDet_eq_det (M : DenseMatrix n n R) :
    DenseMatrix.gaussDet M = M.toMatrix.det := by
  calc
    DenseMatrix.gaussDet M = DeterminantInternal.rawGaussDet M.toMatrix := by
      simp
    _ = M.toMatrix.det :=
      DeterminantInternal.rawGaussDet_eq_det (R := R) (M := M.toMatrix)

end DenseMatrix
