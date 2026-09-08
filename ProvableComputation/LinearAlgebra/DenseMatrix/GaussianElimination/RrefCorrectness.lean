/-
Copyright (c) 2026 Joseph Qian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Qian, Junye Ji, Dhruv Bhatia
-/

import ProvableComputation.LinearAlgebra.DenseMatrix.GaussianElimination.Basic
import ProvableComputation.LinearAlgebra.DenseMatrix.GaussianElimination.Pivot
import ProvableComputation.LinearAlgebra.Matrix.Echelon

/-!
# Gaussian Elimination Correctness

This module proves that the executable row-reduction procedures produce echelon and reduced
row-echelon forms, preserve the appropriate linear-algebraic invariants, and correctly log
their elementary row operations.
-/

namespace DenseMatrix

open GaussianEliminationInternal

variable {α : Type} [Semiring α] [DecidableEq α]
variable {m n : ℕ}

/-! ## Row-operation certificates and execution log theorems -/

variable {α : Type} [Field α]
variable {m n : Nat}

set_option linter.style.longLine false

omit [Field α] in
private lemma swapRow_self (M : DenseMatrix m n α) (r : Fin m) :
    swapRow M r r = M := by
  ext i j
  by_cases h : i = r
  · simp [swapRow, h]
  · simp [swapRow, h]

private lemma factor_one (M : DenseMatrix m n α) (r : Fin m) :
    scaleRow M r 1 = M := by
  ext i j
  by_cases h : i = r
  · simp [scaleRow]
  · simp [scaleRow]

/- Multiplying a matrix by an invertible matrix does not change its solution set -/
lemma mul_by_inv [Inhabited α] [NeZero m] [NeZero n]
    (A : DenseMatrix m m α) (A_inv : DenseMatrix m m α)
    (hA : A_inv * A = (1 : DenseMatrix m m α))
    (M : DenseMatrix m n α) (x : DenseMatrix n 1 α) :
    A * M * x = 0 ↔ M * x = 0 := by
  constructor
  · intro h
    have h1 : A_inv * (A * M * x) = A_inv * (0 : DenseMatrix m 1 α) := by rw [h]
    rw [←DenseMatrix.mul_assoc, ←DenseMatrix.mul_assoc, hA] at h1
    simpa only [DenseMatrix.one_mul, DenseMatrix.mul_zero] using h1
  · intro h
    rw [DenseMatrix.mul_assoc, h, DenseMatrix.mul_zero]

/- Swapping two rows of a `DenseMatrix` does not change the matrix's solution set. -/
lemma swap_proof {x : DenseMatrix n 1 α} [Inhabited α] [NeZero m] [NeZero n]
    (M : DenseMatrix m n α) (r₁ r₂ : Fin m)
    : (swapRow M r₁ r₂) * x = 0 ↔ M * x = 0 := by
  let A_inv : DenseMatrix m m α := ofMatrix (Matrix.swap α r₁ r₂)
  have hA : ofMatrix (Matrix.swap α r₁ r₂) * A_inv = 1 := by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    rw [mul_toMatrix, toMatrix_ofMatrix, Matrix.swap_mul_self, one_toMatrix]
  rw [←toMatrix_inj, ←toMatrix_inj]
  simp only [mul_toMatrix, toMatrix_swap_eq_swap_toMatrix]
  rw [←ofMatrix_inj, ←ofMatrix_inj, ←mul_ofMatrix, ←mul_ofMatrix, ←mul_ofMatrix]
  simp only [ofMatrix_toMatrix]
  exact mul_by_inv A_inv _ hA M x

/-- Scaling a row of a `DenseMatrix` does not change the matrix's solution set. -/
lemma scale_proof {x : DenseMatrix n 1 α} [Inhabited α] [NeZero m] [NeZero n]
    (M : DenseMatrix m n α) (r : Fin m) (c : α)
    (hc : c ≠ 0)
    : (scaleRow M r c) * x = 0 ↔ M * x = 0 := by
  let A_inv : DenseMatrix m m α := ofMatrix (Matrix.transvection r r ((1 - c) / c))
  have hA : A_inv * ofMatrix (Matrix.transvection r r (c - 1)) = 1 := by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    rw [mul_toMatrix, toMatrix_ofMatrix, toMatrix_ofMatrix, one_toMatrix]
    unfold Matrix.transvection
    rw [add_mul, mul_add, mul_add]
    simp only [mul_one, one_mul, Matrix.single_mul_single_same]
    unfold Matrix.single
    ext i j
    by_cases h1 : r = i ∧ r = j <;> by_cases h2 : i = j
    · simp [h1, h2]
      field_simp
      ring_nf
      rw [Matrix.one_apply, if_pos h2]
      exact (mul_one c).symm
    · simp [h1, h2]
    · simp [h2]
      by_cases h3 : r = j
      · simp [h3]
        field_simp
        ring_nf
        rw [Matrix.one_apply, if_pos h2]
        exact (mul_one c).symm
      · simp [h2, h3, Matrix.one_apply]
    · simp [h1]
  rw [←toMatrix_inj, ←toMatrix_inj]
  simp only [mul_toMatrix, toMatrix_scale_eq_scale_toMatrix]
  rw [←ofMatrix_inj, ←ofMatrix_inj, ←mul_ofMatrix, ←mul_ofMatrix, ←mul_ofMatrix]
  simp only [ofMatrix_toMatrix]
  exact mul_by_inv _ A_inv hA M x

/--
Adding a multiple of one row to another row of a `DenseMatrix` does not change the matrix's
solution set.
-/
lemma replace_proof {x : DenseMatrix n 1 α} [Inhabited α] [NeZero m] [NeZero n]
    (M : DenseMatrix m n α)
    (use toReplace : Fin m) (k : α) (h : use ≠ toReplace)
    : (replaceRow M use toReplace k) * x = 0 ↔ M * x = 0 := by
  let A_inv : DenseMatrix m m α := ofMatrix (Matrix.transvection toReplace use (-k))
  have hA : A_inv * ofMatrix (Matrix.transvection toReplace use k) = (1 : DenseMatrix m m α) := by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    rw [mul_toMatrix, toMatrix_ofMatrix, toMatrix_ofMatrix, one_toMatrix, Matrix.transvection_mul_transvection_same]
    · simp only [neg_add_cancel, Matrix.transvection_zero]
    · exact h.symm
  rw [←toMatrix_inj, ←toMatrix_inj]
  simp only [mul_toMatrix, toMatrix_replace_eq_replace_toMatrix]
  rw [←ofMatrix_inj, ←ofMatrix_inj, ←mul_ofMatrix, ←mul_ofMatrix, ←mul_ofMatrix]
  simp only [ofMatrix_toMatrix]
  exact mul_by_inv _ A_inv hA M x

variable [DecidableEq α]

private lemma eliminateColLoopAux_eq
    (pivotRow : Fin m) (pivotCol : Fin n) (pivotVal : α) (r : Nat)
    (M : DenseMatrix m n α) (steps : List (RowOp m α))
    (hpivot : M.get pivotRow pivotCol = pivotVal) :
    eliminateColLoopAux pivotRow pivotCol pivotVal r M steps =
      eliminateColLoop pivotRow pivotCol r M steps := by
  simp [eliminateColLoop, hpivot]

/-- Running `eliminateColLoop` preserves the solution set of the matrix. -/
theorem eliminate_proof_helper [Inhabited α] [NeZero m] [NeZero n]
    (r : Fin m) (c : Fin n) (row : Nat) (M : DenseMatrix m n α)
    (x : DenseMatrix n 1 α) (steps : List (RowOp m α)) (reduced : Bool)
    : (eliminateColLoop r c row M steps).1 * x = 0 ↔ M * x = 0 := by
  rw [eliminateColLoop, eliminateColLoopAux]
  split_ifs with hrow
  · simp only [ne_eq, List.concat_eq_append, ite_not, dite_eq_ite]
    split_ifs with hEq hcoeff
    · simpa [eliminateColLoopAux_eq (pivotRow := r) (pivotCol := c) (pivotVal := M.get r c)
        (r := row + 1) (M := M) (steps := steps) rfl] using
        eliminate_proof_helper r c (row + 1) M x steps reduced
    · simpa [eliminateColLoopAux_eq (pivotRow := r) (pivotCol := c) (pivotVal := M.get r c)
        (r := row + 1) (M := M) (steps := steps) rfl] using
        eliminate_proof_helper r c (row + 1) M x steps reduced
    · let i : Fin m := ⟨row, hrow⟩
      let M' := replaceRow M r i (-M.get i c / M.get r c)
      let steps' := List.concat steps (.replace r i (-M.get i c / M.get r c))
      have huse : r ≠ i := by
        push Not at hEq
        exact hEq.symm
      have hpivot' : M'.get r c = M.get r c := by
        simp [M', replaceRow, huse, of_apply]
      have hrec :
          (eliminateColLoop r c (row + 1) M' steps').1 * x = 0 ↔ M' * x = 0 := by
        simpa [M', steps'] using eliminate_proof_helper r c (row + 1) M' x steps' reduced
      have hrec' :
          (eliminateColLoopAux r c (M.get r c) (row + 1) M' steps').1 * x = 0 ↔ M' * x = 0 := by
        simpa [eliminateColLoopAux_eq (pivotRow := r) (pivotCol := c) (pivotVal := M.get r c)
          (r := row + 1) (M := M') (steps := steps') hpivot'] using hrec
      have hrec'' :
          (eliminateColLoopAux r c (M.get r c) (row + 1)
              (replaceRow M r ⟨row, hrow⟩ (-M.get ⟨row, hrow⟩ c / M.get r c))
              (steps ++ [RowOp.replace r ⟨row, hrow⟩ (-M.get ⟨row, hrow⟩ c / M.get r c)])).1 * x = 0 ↔
            M' * x = 0 := by
        simpa [i, M', steps'] using hrec'
      rw [hrec'', replace_proof]
      exact huse
  · rfl

/-- Running `eliminateCol` preserves the solution set of the matrix. -/
theorem eliminate_proof {x : DenseMatrix n 1 α} [Inhabited α] [NeZero m] [NeZero n]
    (M : DenseMatrix m n α)
    (r : Fin m) (c : Fin n) (steps : List (RowOp m α)) (reduced : Bool)
    : (eliminateCol M r c steps reduced).1 * x = 0 ↔ M * x = 0 := by
  rw [eliminateCol]
  split
  · exact eliminate_proof_helper r c 0 M x steps reduced
  · exact eliminate_proof_helper r c (↑r) M x steps reduced

/- Gaussian elimination does not change the matrix's solution set -/
theorem rref_proof_helper [Inhabited α] [NeZero m] [NeZero n]
    (M : DenseMatrix m n α) (r c : Nat) (x : DenseMatrix n 1 α)
    (steps : List (RowOp m α)) (reduced : Bool)
    : (rowReductionAux M r c steps reduced).1 * x = 0 ↔ M * x = 0 := by
  rw [rowReductionAux]
  split_ifs with h1 h2
  · simp only [List.concat_eq_append, List.append_assoc, List.cons_append, List.nil_append]
    split
    · rfl
    rw [rref_proof_helper, eliminate_proof]
    split_ifs with h3 h4 h5
    · rfl
    · rw [scale_proof]
      rename_i pivotRow pivotCol heq
      have hr : pivotRow = ⟨r, h1⟩ := by
        ext
        exact h3
      rw [← hr]
      rw [ne_eq, inv_eq_iff_eq_inv, _root_.inv_zero]
      exact checkPivot_some_nonzero (M := M) r c heq
    · rw [swap_proof]
    rw [scale_proof, swap_proof]
    rename_i pivotRow pivotCol heq
    rw [swapRow, of_apply]
    split_ifs with h6 h7
    · rw [ne_eq, inv_eq_iff_eq_inv, _root_.inv_zero]
      exact checkPivot_some_nonzero (M := M) r c heq
    · rw [h7]
      rw [ne_eq, inv_eq_iff_eq_inv, _root_.inv_zero]
      exact checkPivot_some_nonzero (M := M) r c heq
    · contradiction
  · rfl
  rfl

theorem ref_proof [Inhabited α] [NeZero m] [NeZero n]
    (M : DenseMatrix m n α) (x : DenseMatrix n 1 α) :
    (rowEchelonForm M).1 * x = 0 ↔ M * x = 0 := by
  rw [rowEchelonForm]
  exact rref_proof_helper M 0 0 x List.nil false

theorem rref_proof [Inhabited α] [NeZero m] [NeZero n]
    (M : DenseMatrix m n α) (x : DenseMatrix n 1 α) :
    (reducedRowEchelonForm M).1 * x = 0 ↔ M * x = 0 := by
  rw [reducedRowEchelonForm]
  exact rref_proof_helper M 0 0 x List.nil true

/-- The helper function `eliminateColLoop` does not decrease the length of the steps list. -/
private theorem elim_col_go_adds_steps_helper (pivotRow : Fin m) (pivotCol : Fin n) (r : Nat)
    (M : DenseMatrix m n α) (steps : List (RowOp m α)) :
    (eliminateColLoop pivotRow pivotCol r M steps).2.length ≥ steps.length := by
  rw [eliminateColLoop, eliminateColLoopAux]
  split_ifs with hrow
  · simp only [ne_eq, List.concat_eq_append, ite_not, dite_eq_ite]
    split_ifs with hEq hcoeff
    · simpa [eliminateColLoopAux_eq (pivotRow := pivotRow) (pivotCol := pivotCol)
        (pivotVal := M.get pivotRow pivotCol) (r := r + 1) (M := M) (steps := steps) rfl] using
        elim_col_go_adds_steps_helper pivotRow pivotCol (r + 1) M steps
    · simpa [eliminateColLoopAux_eq (pivotRow := pivotRow) (pivotCol := pivotCol)
        (pivotVal := M.get pivotRow pivotCol) (r := r + 1) (M := M) (steps := steps) rfl] using
        elim_col_go_adds_steps_helper pivotRow pivotCol (r + 1) M steps
    · let i : Fin m := ⟨r, hrow⟩
      let M' := replaceRow M pivotRow i (-M.get i pivotCol / M.get pivotRow pivotCol)
      let steps' := steps ++ [RowOp.replace pivotRow i (-M.get i pivotCol / M.get pivotRow pivotCol)]
      have huse : pivotRow ≠ i := by
        push Not at hEq
        exact hEq.symm
      have hpivot' : M'.get pivotRow pivotCol = M.get pivotRow pivotCol := by
        simp [M', replaceRow, huse, of_apply]
      have hrec :
          (eliminateColLoop pivotRow pivotCol (r + 1) M' steps').2.length ≥ steps'.length := by
        simpa [M', steps'] using
          elim_col_go_adds_steps_helper pivotRow pivotCol (r + 1) M' steps'
      have hrec' :
          (eliminateColLoopAux pivotRow pivotCol (M.get pivotRow pivotCol) (r + 1) M' steps').2.length ≥
            steps'.length := by
        simpa [eliminateColLoopAux_eq (pivotRow := pivotRow) (pivotCol := pivotCol)
          (pivotVal := M.get pivotRow pivotCol) (r := r + 1) (M := M') (steps := steps') hpivot'] using hrec
      trans steps'.length
      · exact hrec'
      · aesop
  · simp

lemma elim_col_go_adds_steps (pivotRow : Fin m) (pivotCol : Fin n) (r : Nat)
    (M : DenseMatrix m n α) (l1 l2 : List (RowOp m α)) :
    (eliminateColLoop pivotRow pivotCol r M (l1 ++ l2)).2.length ≥ l1.length := by
  trans (l1 ++ l2).length
  · exact elim_col_go_adds_steps_helper pivotRow pivotCol r M (l1 ++ l2)
  · aesop

lemma elim_col_adds_steps (M : DenseMatrix m n α) (pivotRow : Fin m) (pivotCol : Fin n)
    (l1 l2 : List (RowOp m α)) (reduced : Bool) :
    (eliminateCol M pivotRow pivotCol (l1 ++ l2) reduced).2.length ≥ l1.length := by
  rw [eliminateCol]
  split_ifs
  · exact elim_col_go_adds_steps pivotRow pivotCol 0 M l1 l2
  · exact elim_col_go_adds_steps pivotRow pivotCol (↑pivotRow) M l1 l2

theorem row_reduction_adds_steps (M : DenseMatrix m n α) (r c : Nat)
    (steps : List (RowOp m α)) (reduced : Bool) :
    (rowReductionAux M r c steps reduced).2.length >= steps.length := by
  rw [rowReductionAux]
  split_ifs with hrow hcol
  · cases hcp : checkPivot M r c with
    | none =>
        simpa only [hcp] using (show steps.length ≥ steps.length from le_rfl)
    | some p =>
        rcases p with ⟨pivotRow, pivotCol⟩
        simp only [List.concat_eq_append, List.append_assoc]
        split_ifs with hswap hpivot
        · let rowFin : Fin m := ⟨r, hrow⟩
          let res := eliminateCol M rowFin pivotCol
            (steps ++ [RowOp.swap rowFin pivotRow])
            reduced
          trans res.2.length
          · exact row_reduction_adds_steps res.1 (r + 1) (c + 1) res.2 reduced
          · unfold res
            exact elim_col_adds_steps M rowFin pivotCol steps [RowOp.swap rowFin pivotRow] reduced
        · let rowFin : Fin m := ⟨r, hrow⟩
          let res := eliminateCol (scaleRow M rowFin (M.get rowFin pivotCol)⁻¹) rowFin pivotCol
            (steps ++
              ([RowOp.swap rowFin pivotRow] ++ [RowOp.factor rowFin (M.get rowFin pivotCol)⁻¹]))
            reduced
          trans res.2.length
          · exact row_reduction_adds_steps res.1 (r + 1) (c + 1) res.2 reduced
          · unfold res
            exact elim_col_adds_steps (scaleRow M rowFin (M.get rowFin pivotCol)⁻¹) rowFin pivotCol
              steps
              ([RowOp.swap rowFin pivotRow] ++ [RowOp.factor rowFin (M.get rowFin pivotCol)⁻¹])
              reduced
        · let rowFin : Fin m := ⟨r, hrow⟩
          let res := eliminateCol (swapRow M rowFin pivotRow) rowFin pivotCol
            (steps ++ [RowOp.swap rowFin pivotRow])
            reduced
          trans res.2.length
          · exact row_reduction_adds_steps res.1 (r + 1) (c + 1) res.2 reduced
          · unfold res
            exact elim_col_adds_steps (swapRow M rowFin pivotRow) rowFin pivotCol steps
              [RowOp.swap rowFin pivotRow] reduced
        · let rowFin : Fin m := ⟨r, hrow⟩
          let swapped := swapRow M rowFin pivotRow
          let res := eliminateCol (scaleRow swapped rowFin (swapped.get rowFin pivotCol)⁻¹) rowFin
            pivotCol
            (steps ++
              ([RowOp.swap rowFin pivotRow] ++ [RowOp.factor rowFin (swapped.get rowFin pivotCol)⁻¹]))
            reduced
          trans res.2.length
          · exact row_reduction_adds_steps res.1 (r + 1) (c + 1) res.2 reduced
          · unfold res
            exact elim_col_adds_steps
              (scaleRow swapped rowFin (swapped.get rowFin pivotCol)⁻¹) rowFin pivotCol steps
              ([RowOp.swap rowFin pivotRow] ++
                [RowOp.factor rowFin (swapped.get rowFin pivotCol)⁻¹])
              reduced
  · exact le_rfl
  · exact le_rfl

private theorem eliminateCol_go_log_correct
    (pivotRow : Fin m) (pivotCol : Fin n) (r : Nat)
    (M : DenseMatrix m n α) (steps : List (RowOp m α)) :
    ∃ ops_tail : List (RowOp m α),
      eliminateColLoop pivotRow pivotCol r M steps =
        (ops_tail.foldl applyRowOp M, steps ++ ops_tail) := by
  have hrec :
      ∀ k (r : Nat) (M : DenseMatrix m n α) (steps : List (RowOp m α)),
        m - r = k →
          ∃ ops_tail : List (RowOp m α),
            eliminateColLoop pivotRow pivotCol r M steps =
              (ops_tail.foldl applyRowOp M, steps ++ ops_tail) := by
    intro k
    induction k with
    | zero =>
        intro r M steps hk
        have hr : m ≤ r := Nat.le_of_sub_eq_zero hk
        refine ⟨[], ?_⟩
        rw [eliminateColLoop, eliminateColLoopAux, dif_neg (not_lt_of_ge hr)]
        simp
    | succ k ih =>
        intro r M steps hk
        have hr : r < m := by omega
        have hk' : m - (r + 1) = k := by omega
        let i : Fin m := ⟨r, hr⟩
        rw [eliminateColLoop, eliminateColLoopAux, dif_pos hr]
        by_cases hEq : i = pivotRow
        · obtain ⟨ops_tail, htail⟩ := ih (r + 1) M steps hk'
          exact ⟨ops_tail, by simpa [i, hEq, dite_eq_ite, eliminateColLoop] using htail⟩
        · by_cases hcoeff : M.get i pivotCol ≠ 0
          · let op : RowOp m α := .replace pivotRow i (-M.get i pivotCol / M.get pivotRow pivotCol)
            let M' := replaceRow M pivotRow i (-M.get i pivotCol / M.get pivotRow pivotCol)
            let steps' := steps ++ [op]
            have huse : pivotRow ≠ i := by
              intro hpr
              exact hEq hpr.symm
            have hpivot' : M'.get pivotRow pivotCol = M.get pivotRow pivotCol := by
              simp [M', replaceRow, huse, of_apply]
            obtain ⟨ops_tail, htail⟩ := ih (r + 1) M' steps' hk'
            refine ⟨op :: ops_tail, ?_⟩
            simpa [i, hEq, hcoeff, op, M', steps', List.foldl_append, List.append_assoc,
              applyRowOp, dite_eq_ite, eliminateColLoopAux_eq (pivotRow := pivotRow)
              (pivotCol := pivotCol) (pivotVal := M.get pivotRow pivotCol) (r := r + 1)
              (M := M') (steps := steps') hpivot'] using htail
          · obtain ⟨ops_tail, htail⟩ := ih (r + 1) M steps hk'
            exact ⟨ops_tail, by
              simpa [i, hEq, hcoeff, dite_eq_ite, eliminateColLoop,
                eliminateColLoopAux_eq (pivotRow := pivotRow) (pivotCol := pivotCol)
                  (pivotVal := M pivotRow pivotCol) (r := r + 1) (M := M) (steps := steps) rfl] using htail⟩
  exact hrec (m - r) r M steps rfl

private theorem eliminateCol_log_correct
    (M : DenseMatrix m n α) (pivotRow : Fin m) (pivotCol : Fin n)
    (steps : List (RowOp m α)) (reduced : Bool) :
    ∃ ops_tail : List (RowOp m α),
      eliminateCol M pivotRow pivotCol steps reduced =
        (ops_tail.foldl applyRowOp M, steps ++ ops_tail) := by
  rw [eliminateCol]
  by_cases hred : reduced
  · simpa [hred] using eliminateCol_go_log_correct pivotRow pivotCol 0 M steps
  · simpa [hred] using eliminateCol_go_log_correct pivotRow pivotCol pivotRow.1 M steps

private theorem rrefAux_log_correct
    (M : DenseMatrix m n α) (r c : Nat)
    (steps : List (RowOp m α)) (reduced : Bool) :
    ∃ ops_tail : List (RowOp m α),
      rowReductionAux M r c steps reduced =
        (ops_tail.foldl applyRowOp M, steps ++ ops_tail) := by
  have hrec :
      ∀ k (M : DenseMatrix m n α) (r c : Nat)
        (steps : List (RowOp m α)) (reduced : Bool),
        m - r = k →
          ∃ ops_tail : List (RowOp m α),
            rowReductionAux M r c steps reduced =
              (ops_tail.foldl applyRowOp M, steps ++ ops_tail) := by
    intro k
    induction k with
    | zero =>
        intro M r c steps reduced hk
        have hr : m ≤ r := Nat.le_of_sub_eq_zero hk
        refine ⟨[], ?_⟩
        simp [rowReductionAux, Nat.not_lt_of_ge hr]
    | succ k ih =>
        intro M r c steps reduced hk
        have hr : r < m := by omega
        have hk' : m - (r + 1) = k := by omega
        rw [rowReductionAux, dif_pos hr]
        by_cases hc : c < n
        · rw [if_pos hc]
          cases hcp : checkPivot M r c with
          | none =>
              refine ⟨[], ?_⟩
              simp
          | some p =>
              rcases p with ⟨pivotRow, pivotCol⟩
              let rowFin : Fin m := ⟨r, hr⟩
              let swapOp : RowOp m α := .swap rowFin pivotRow
              let steps1 : List (RowOp m α) := steps ++ [swapOp]
              let m1 : DenseMatrix m n α :=
                if pivotRow.1 = r then M else swapRow M rowFin pivotRow
              have hm1 : m1 = applyRowOp M swapOp := by
                by_cases hswap : pivotRow.1 = r
                · have hpiv : pivotRow = rowFin := by
                    ext
                    simpa [rowFin] using hswap
                  subst hpiv
                  simp [m1, swapOp, applyRowOp, rowFin, swapRow_self]
                · simp [m1, swapOp, applyRowOp, hswap]
              let pivotVal : α := m1.get rowFin pivotCol
              let factorOp : RowOp m α := .factor rowFin pivotVal⁻¹
              cases hred : reduced with
              | false =>
                  obtain ⟨ops_elim, hElim⟩ :=
                    eliminateCol_log_correct m1 rowFin pivotCol steps1 false
                  obtain ⟨ops_rec, hRec⟩ :=
                    ih (ops_elim.foldl applyRowOp m1) (r + 1) (c + 1) (steps1 ++ ops_elim) false hk'
                  refine ⟨[swapOp] ++ ops_elim ++ ops_rec, ?_⟩
                  have hbranch :
                      (match eliminateCol m1 rowFin pivotCol steps1 false with
                        | (m3, steps3) => rowReductionAux m3 (r + 1) (c + 1) steps3 false) =
                        (ops_rec.foldl applyRowOp (ops_elim.foldl applyRowOp m1),
                          steps1 ++ ops_elim ++ ops_rec) := by
                    simpa [hElim] using hRec
                  have hfinal :
                      (ops_rec.foldl applyRowOp (ops_elim.foldl applyRowOp m1),
                        steps1 ++ ops_elim ++ ops_rec) =
                        (List.foldl applyRowOp M ([swapOp] ++ ops_elim ++ ops_rec),
                          steps ++ ([swapOp] ++ ops_elim ++ ops_rec)) := by
                    apply Prod.ext
                    · simp only [List.cons_append, List.nil_append, List.foldl_cons,
                        List.foldl_append]
                      rw [hm1]
                    · simp [steps1, List.append_assoc]
                  simpa [hcp, rowFin, hred, steps1, m1, pivotVal, List.concat_eq_append] using
                    hbranch.trans hfinal
              | true =>
                  by_cases hpv : pivotVal = 1
                  · obtain ⟨ops_elim, hElim⟩ :=
                      eliminateCol_log_correct m1 rowFin pivotCol steps1 true
                    obtain ⟨ops_rec, hRec⟩ :=
                      ih (ops_elim.foldl applyRowOp m1) (r + 1) (c + 1) (steps1 ++ ops_elim)
                        true hk'
                    refine ⟨[swapOp] ++ ops_elim ++ ops_rec, ?_⟩
                    have hbranch :
                        (match eliminateCol m1 rowFin pivotCol steps1 true with
                          | (m3, steps3) => rowReductionAux m3 (r + 1) (c + 1) steps3 true) =
                          (ops_rec.foldl applyRowOp (ops_elim.foldl applyRowOp m1),
                            steps1 ++ ops_elim ++ ops_rec) := by
                      simpa [hElim] using hRec
                    have hfinal :
                        (ops_rec.foldl applyRowOp (ops_elim.foldl applyRowOp m1),
                          steps1 ++ ops_elim ++ ops_rec) =
                          (List.foldl applyRowOp M ([swapOp] ++ ops_elim ++ ops_rec),
                            steps ++ ([swapOp] ++ ops_elim ++ ops_rec)) := by
                      apply Prod.ext
                      · simp only [List.cons_append, List.nil_append, List.foldl_cons,
                          List.foldl_append]
                        rw [hm1]
                      · simp [steps1, List.append_assoc]
                    simpa [hcp, rowFin, hred, hpv, steps1, m1, pivotVal, List.concat_eq_append]
                      using hbranch.trans hfinal
                  · let steps2 : List (RowOp m α) := steps1 ++ [factorOp]
                    let m2 : DenseMatrix m n α := scaleRow m1 rowFin pivotVal⁻¹
                    have hm2 : m2 = applyRowOp m1 factorOp := by
                      simp [m2, factorOp, applyRowOp]
                    obtain ⟨ops_elim, hElim⟩ :=
                      eliminateCol_log_correct m2 rowFin pivotCol steps2 true
                    obtain ⟨ops_rec, hRec⟩ :=
                      ih (ops_elim.foldl applyRowOp m2) (r + 1) (c + 1) (steps2 ++ ops_elim)
                        true hk'
                    refine ⟨[swapOp, factorOp] ++ ops_elim ++ ops_rec, ?_⟩
                    have hbranch :
                        (match eliminateCol m2 rowFin pivotCol steps2 true with
                          | (m3, steps3) => rowReductionAux m3 (r + 1) (c + 1) steps3 true) =
                          (ops_rec.foldl applyRowOp (ops_elim.foldl applyRowOp m2),
                            steps2 ++ ops_elim ++ ops_rec) := by
                      simpa [hElim] using hRec
                    have hfinal :
                        (ops_rec.foldl applyRowOp (ops_elim.foldl applyRowOp m2),
                          steps2 ++ ops_elim ++ ops_rec) =
                          (List.foldl applyRowOp M ([swapOp, factorOp] ++ ops_elim ++ ops_rec),
                            steps ++ ([swapOp, factorOp] ++ ops_elim ++ ops_rec)) := by
                      apply Prod.ext
                      · simp only [List.cons_append, List.nil_append, List.foldl_cons,
                          List.foldl_append]
                        rw [hm2, hm1]
                      · simp [steps1, steps2, List.append_assoc]
                    simpa [hcp, rowFin, hred, hpv, steps1, m1, pivotVal, steps2, m2,
                      List.concat_eq_append] using hbranch.trans hfinal
        · refine ⟨[], ?_⟩
          simp [hc]
  exact hrec (m - r) M r c steps reduced rfl

/--
If the `steps` certificate is empty, then the resulting matrix is the same as the source
matrix.
-/
lemma empty_list_iff_no_change (M M' : DenseMatrix m n α) (r c : Nat)
    (ops : List (RowOp m α)) (reduced : Bool)
    : rowReductionAux M r c ops reduced = (M', []) → M = M' := by
  intro h
  obtain ⟨ops_tail, hlog⟩ := rrefAux_log_correct M r c ops reduced
  rw [hlog] at h
  injection h with hM hOps
  have hnil : ops_tail = [] := (List.eq_nil_of_append_eq_nil hOps).2
  simpa [hnil] using hM

theorem steps_helper (M M' : DenseMatrix m n α) (r c : Nat)
    (ops_head ops_tail ops_final : List (RowOp m α)) (reduced : Bool)
    (h_ops : ops_final = ops_head ++ ops_tail)
    : rowReductionAux M r c ops_head reduced = (M', ops_head ++ ops_tail) →
        ops_tail.foldl applyRowOp M = M' := by
  intro h
  have h' : rowReductionAux M r c ops_head reduced = (M', ops_final) := by
    simpa [h_ops] using h
  obtain ⟨ops_tail', hlog⟩ := rrefAux_log_correct M r c ops_head reduced
  rw [hlog] at h'
  injection h' with hM hOps
  have hOps' : ops_head ++ ops_tail' = ops_head ++ ops_tail := by
    simpa [h_ops] using hOps
  have htail : ops_tail' = ops_tail := (List.append_right_inj ops_head).mp hOps'
  simpa [htail] using hM

private theorem rowEchelonForm_steps_helper (M M' : DenseMatrix m n α) (ops : List (RowOp m α))
    : rowEchelonForm M = { matrix := M', steps := ops } → ops.foldl applyRowOp M = M' := by
  intro h
  have h_ops : ops = [] ++ ops := by simp
  have h' : rowReductionAux M 0 0 [] false = (M', [] ++ ops) := by
    simp only [List.nil_append]
    unfold rowEchelonForm at h
    injection h with h_matrix h_steps
    rw [← h_matrix, ← h_steps]
  simpa using steps_helper M M' 0 0 [] ops ops false h_ops h'

private theorem reducedRowEchelonForm_steps_helper (M M' : DenseMatrix m n α)
    (ops : List (RowOp m α))
    : reducedRowEchelonForm M = { matrix := M', steps := ops } → ops.foldl applyRowOp M = M' := by
  intro h
  have h_ops : ops = [] ++ ops := by simp
  have h' : rowReductionAux M 0 0 [] true = (M', [] ++ ops) := by
    simp only [List.nil_append]
    unfold reducedRowEchelonForm at h
    injection h with h_matrix h_steps
    rw [← h_matrix, ← h_steps]
  simpa using steps_helper M M' 0 0 [] ops ops true h_ops h'

/-- Applying the `RowOps` in the certificate to the source matrix returns the resulting matrix. -/
theorem rowEchelonForm_steps
    (M : DenseMatrix m n α) :
    (rowEchelonForm M).steps.foldl applyRowOp M = (rowEchelonForm M).matrix := by
  simpa [rowEchelonForm] using
    (rowEchelonForm_steps_helper
      (M := M)
      (M' := (rowEchelonForm M).1)
      (ops := (rowEchelonForm M).2)
      rfl)

theorem reducedRowEchelonForm_steps
    (M : DenseMatrix m n α) :
    (reducedRowEchelonForm M).steps.foldl applyRowOp M =
      (reducedRowEchelonForm M).matrix := by
  simpa [reducedRowEchelonForm] using
    (reducedRowEchelonForm_steps_helper
      (M := M)
      (M' := (reducedRowEchelonForm M).1)
      (ops := (reducedRowEchelonForm M).2)
      rfl)

-- /-! ## Algorithm output is (reduced) row echelon form of input -/

-- /--
-- Core invariance lemma for `GaussianEliminationInternal.eliminateColLoop`.

-- No matter which branch is taken while scanning rows (skip pivot row, replace,
-- or continue), the matrix stays row-equivalent to the input `cur`.
-- -/
-- private theorem eliminateColGo_rowEquivalent
--     {m n : Nat}
--     (pivotRow : Fin m) (pivotCol : Fin n) (row : Nat)
--     (cur : DenseMatrix m n α) (steps : List (RowOp m α)) :
--     Matrix.RowEquivalent cur.toMatrix (eliminateColLoop pivotRow pivotCol row cur steps).1.toMatrix := by
--   have goAux_matrix_eq
--       (pivotVal : α) (row : Nat) (cur : DenseMatrix m n α) (steps : List (RowOp m α))
--       (hpivot : cur.get pivotRow pivotCol = pivotVal) :
--       (eliminateColLoopAux pivotRow pivotCol pivotVal row cur steps).1 =
--         (eliminateColLoop pivotRow pivotCol row cur steps).1 := by
--     simp [eliminateColLoop, hpivot]
--   rw [eliminateColLoop, eliminateColLoopAux]
--   split_ifs with hr
--   · let i : Fin m := ⟨row, hr⟩
--     by_cases hEq : i = pivotRow
--     · have hrec : Matrix.RowEquivalent cur.toMatrix
--           (eliminateColLoop pivotRow pivotCol (row + 1) cur steps).1.toMatrix := by
--         exact eliminateColGo_rowEquivalent pivotRow pivotCol (row + 1) cur steps
--       have hrec' : Matrix.RowEquivalent cur.toMatrix
--             (eliminateColLoopAux pivotRow pivotCol (cur.get pivotRow pivotCol) (row + 1) cur steps).1.toMatrix := by
--         simpa [goAux_matrix_eq (cur.get pivotRow pivotCol) (row + 1) cur steps rfl] using hrec
--       simpa [i, hEq] using hrec'
--     · by_cases hcoeff : cur.get i pivotCol ≠ 0
--       · let cur' := replaceRow cur pivotRow i (-cur.get i pivotCol / cur.get pivotRow pivotCol)
--         let steps' := List.concat steps (.replace pivotRow i (-cur.get i pivotCol / cur.get pivotRow pivotCol))
--         have hreplace : Matrix.RowEquivalent cur.toMatrix cur'.toMatrix := by
--           dsimp [cur']
--           rw [toMatrix_replace_eq_replace_toMatrix]
--           exact Matrix.rowEquivalent_transvection cur.toMatrix i pivotRow hEq
--             (-cur.get i pivotCol / cur.get pivotRow pivotCol)
--         have hpivot' : cur'.get pivotRow pivotCol = cur.get pivotRow pivotCol := by
--           have huse : pivotRow ≠ i := by
--             intro hpr
--             exact hEq hpr.symm
--           simp [cur', replaceRow, huse, of_apply]
--         have hrec : Matrix.RowEquivalent cur'.toMatrix
--               (eliminateColLoop pivotRow pivotCol (row + 1) cur' steps').1.toMatrix := by
--           simpa [cur', steps'] using
--             (eliminateColGo_rowEquivalent pivotRow pivotCol (row + 1) cur' steps')
--         have hrec' : Matrix.RowEquivalent cur'.toMatrix
--             (eliminateColLoopAux pivotRow pivotCol (cur.get pivotRow pivotCol) (row + 1) cur' steps').1.toMatrix := by
--           simpa [goAux_matrix_eq (cur.get pivotRow pivotCol) (row + 1) cur' steps' hpivot'] using hrec
--         simpa [i, hEq, hcoeff, cur', steps'] using Matrix.RowEquivalent.trans hreplace hrec'
--       · have hrec : Matrix.RowEquivalent cur.toMatrix
--             (eliminateColLoop pivotRow pivotCol (row + 1) cur steps).1.toMatrix := by
--           exact eliminateColGo_rowEquivalent pivotRow pivotCol (row + 1) cur steps
--         have hrec' : Matrix.RowEquivalent cur.toMatrix
--               (eliminateColLoopAux pivotRow pivotCol (cur.get pivotRow pivotCol) (row + 1) cur steps).1.toMatrix := by
--           simpa [goAux_matrix_eq (cur.get pivotRow pivotCol) (row + 1) cur steps rfl] using hrec
--         simpa [i, hEq, hcoeff] using hrec'
--   · simp

-- /--
-- Wrapper lemma for `GaussianEliminationInternal.eliminateCol`.

-- The boolean `reduced` only changes the starting scan row; both branches are
-- delegated to `eliminateColGo_rowEquivalent`.
-- -/
-- private theorem eliminateCol_rowEquivalent
--     {m n : Nat}
--     (M : DenseMatrix m n α) (pivotRow : Fin m) (pivotCol : Fin n)
--     (steps : List (RowOp m α)) (reduced : Bool) :
--     Matrix.RowEquivalent M.toMatrix (eliminateCol M pivotRow pivotCol steps reduced).1.toMatrix := by
--   rw [GaussianEliminationInternal.eliminateCol]
--   by_cases hred : reduced
--   · simpa [hred] using eliminateColGo_rowEquivalent pivotRow pivotCol 0 M steps
--   · simpa [hred] using eliminateColGo_rowEquivalent pivotRow pivotCol pivotRow.1 M steps
-- /--
-- Main bridge lemma for the RREF driver `GaussianEliminationInternal.rowReductionAux`.

-- Each algorithmic stage preserves row-equivalence:
-- `M -> m1` (optional swap), `m1 -> m2` (optional normalization),
-- `m2 -> m3` (column elimination), then recursive call on `(row+1, col+1)`.
-- -/
-- private theorem rrefAux_rowEquivalent
--     {m n : Nat}
--     (M : DenseMatrix m n α) (row col : Nat)
--     (steps : List (RowOp m α)) (reduced : Bool) :
--     Matrix.RowEquivalent M.toMatrix (rowReductionAux M row col steps reduced).1.toMatrix := by
--   rw [GaussianEliminationInternal.rowReductionAux.eq_1]
--   split_ifs with hrow hcol
--   · cases hcp : checkPivot M row col with
--     | none =>
--         simp only
--         exact Matrix.RowEquivalent.refl M.toMatrix
--     | some prpc =>
--         rcases prpc with ⟨pivotRow, pivotCol⟩
--         let rowFin : Fin m := ⟨row, hrow⟩
--         let m1 : DenseMatrix m n α :=
--           if pivotRow.1 = row then M else swapRow M rowFin pivotRow
--         let steps1 : List (RowOp m α) := List.concat steps (.swap rowFin pivotRow)
--         let pivotVal : α := m1.get rowFin pivotCol
--         let m2 : DenseMatrix m n α :=
--           if !reduced || pivotVal = 1 then m1 else scaleRow m1 rowFin pivotVal⁻¹
--         let steps2 : List (RowOp m α) :=
--           if !reduced || pivotVal = 1 then
--             steps1
--           else
--             List.concat steps1 (.factor rowFin pivotVal⁻¹)
--         have hM1 : Matrix.RowEquivalent M.toMatrix m1.toMatrix := by
--           by_cases hp : pivotRow.1 = row
--           · simp [m1, hp]
--           · simpa [m1, hp, toMatrix_swap_eq_swap_toMatrix]
--               using (Matrix.rowEquivalent_swap M.toMatrix rowFin pivotRow)
--         have hpivot_ne_zero : pivotVal ≠ 0 := by
--           have hnon : M.get pivotRow pivotCol ≠ 0 :=
--             checkPivot_some_nonzero M row col (by simp [hcp])
--           by_cases hp : pivotRow.1 = row
--           · have hroweq : rowFin = pivotRow := by
--               exact Fin.ext (by simpa [rowFin] using hp.symm)
--             subst hroweq
--             simpa [m1, hp, pivotVal] using hnon
--           · have hrowne : rowFin ≠ pivotRow := by
--               intro hEq
--               exact hp (by simpa [rowFin] using (congrArg Fin.val hEq).symm)
--             have hpres :
--                 (swapRow M rowFin pivotRow).get rowFin pivotCol = M.get pivotRow pivotCol := by
--               simp [swapRow, of_apply]
--             simpa [m1, hp, pivotVal, hpres] using hnon
--         have hM2 : Matrix.RowEquivalent m1.toMatrix m2.toMatrix := by
--           cases hred : reduced with
--           | false =>
--               simp [m2, hred]
--           | true =>
--               by_cases hv : pivotVal = 1
--               · simp [m2, hred, hv]
--               · have hfac : Matrix.RowEquivalent m1.toMatrix (scaleRow m1 rowFin pivotVal⁻¹).toMatrix := by
--                   simpa [toMatrix_scale_eq_scale_toMatrix]
--                     using Matrix.rowEquivalent_rowScale m1.toMatrix rowFin
--                     (Units.mk0 (pivotVal⁻¹) (inv_ne_zero hpivot_ne_zero))
--                   sorry
--                 simpa [m2, hred, hv] using hfac
--         cases hp : GaussianEliminationInternal.eliminateCol m2 rowFin pivotCol steps2 reduced with
--         | mk m3 steps3 =>
--             have hM3raw : Matrix.RowEquivalent m2.toMatrix
--                 (eliminateCol m2 rowFin pivotCol steps2 reduced).1.toMatrix := by
--               simpa using eliminateCol_rowEquivalent m2 rowFin pivotCol steps2 reduced
--             have hRec : Matrix.RowEquivalent m3.toMatrix
--                 (rowReductionAux m3 (row + 1) (col + 1) steps3 reduced).1.toMatrix := by
--               simpa using rrefAux_rowEquivalent m3 (row + 1) (col + 1) steps3 reduced
--             have hRecraw :
--                 Matrix.RowEquivalent (eliminateCol m2 rowFin pivotCol steps2 reduced).1.toMatrix
--                   (rowReductionAux
--                     (eliminateCol m2 rowFin pivotCol steps2 reduced).1
--                     (row + 1) (col + 1)
--                     (eliminateCol m2 rowFin pivotCol steps2 reduced).2 reduced).1.toMatrix := by
--               simpa [hp] using hRec
--             simpa [m1, m2, steps1, steps2, pivotVal, rowFin, hcp, hp, List.concat_eq_append] using
--               Matrix.RowEquivalent.trans (Matrix.RowEquivalent.trans hM1 (Matrix.RowEquivalent.trans hM2 hM3raw)) hRecraw
--   · simp only
--     exact Matrix.RowEquivalent.refl M.toMatrix
--   · simp only
--     exact Matrix.RowEquivalent.refl M.toMatrix
-- termination_by m - row
-- decreasing_by
--   · omega

-- /--
-- Top-level algorithmic invariant.

-- `GaussianEliminationInternal.rawReducedRowEchelonForm` always returns a matrix row-equivalent to its input.
-- -/
-- theorem reducedRowEchelonForm_rowEquivalent
--     {m n : Nat}
--     (A : DenseMatrix m n α) :
--     Matrix.RowEquivalent A.toMatrix (reducedRowEchelonForm A).1.toMatrix := by
--   simpa [reducedRowEchelonForm] using rrefAux_rowEquivalent A 0 0 List.nil true




-- /--
-- Bridge theorem from algorithm output to semantic predicate:
-- the computed output is both row-equivalent to `A` and reduced.
-- -/
-- theorem reducedRowEchelonForm_isReducedEchelonFormOf
--     {m n : Nat}
--     (A : DenseMatrix m n α) :
--     Matrix.IsReducedRowEchelonOf A.toMatrix (reducedRowEchelonForm A).1.toMatrix := by
--   refine ⟨reducedRowEchelonForm_rowEquivalent A, ?_⟩
--   simpa [reducedRowEchelonForm] using
--     Matrix.reducedRowEchelonForm_isReducedEchelonForm A

-- /--
-- Auxiliary bridge theorem: algorithm output is also in echelon form.

-- This is weaker than reduced form but useful when a statement only requires
-- `IsEchelonFormOf`.
-- -/
-- theorem reducedRowEchelonForm_isEchelonFormOf
--     {m n : Nat}
--     (A : Matrix (Fin m) (Fin n) R) :
--     IsEchelonFormOf (A := A) ((GaussianEliminationInternal.rawReducedRowEchelonForm A).1) := by
--   refine ⟨reducedRowEchelonForm_rowEquivalent (A := A), ?_⟩
--   simpa [Matrix.reducedRowEchelonForm] using
--     Matrix.reducedRowEchelonForm_isEchelonForm (M := A)

-- /--
-- If two matrices have the same computed RREF, then they are row-equivalent.
-- -/
-- theorem rowEquivalent_of_rref_eq {m n : Nat}
--     {A B : Matrix (Fin m) (Fin n) R}
--     (hEq : (GaussianEliminationInternal.rawReducedRowEchelonForm A).1 = (GaussianEliminationInternal.rawReducedRowEchelonForm B).1) :
--     RowEquivalent A B := by
--   let C : Matrix (Fin m) (Fin n) R := (GaussianEliminationInternal.rawReducedRowEchelonForm A).1
--   have hAC : RowEquivalent A C := by
--     simpa [C] using reducedRowEchelonForm_rowEquivalent (A := A)
--   have hBC : RowEquivalent B C := by
--     simpa [C, hEq] using reducedRowEchelonForm_rowEquivalent (A := B)
--   exact RowEquivalent.trans hAC (RowEquivalent.symm hBC)

-- /--
-- Computational wrapper: if `decide` confirms RREF equality, conclude row-equivalence.
-- -/
-- theorem rowEquivalent_of_decide_rref_eq_true {m n : Nat}
--     {A B : Matrix (Fin m) (Fin n) R}
--     (hEq : decide ((GaussianEliminationInternal.rawReducedRowEchelonForm A).1 = (GaussianEliminationInternal.rawReducedRowEchelonForm B).1) = true) :
--     RowEquivalent A B := by
--   exact rowEquivalent_of_rref_eq (A := A) (B := B) (of_decide_eq_true hEq)

end DenseMatrix
