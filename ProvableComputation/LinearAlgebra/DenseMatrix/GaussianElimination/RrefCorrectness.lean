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
open scoped Matrix

variable {α : Type*} [Semiring α] [DecidableEq α]
variable {m n : ℕ}

/-! ## Row-operation certificates and execution log theorems -/

variable {α : Type*} [Field α]
variable {m n : Nat}

omit [Field α] in
private lemma swapRow_self (M : DenseMatrix m n α) (r : Fin m) :
    swapRow M r r = M := by
  ext i j
  by_cases h : i = r
  · simp [swapRow, h]
  · simp [swapRow, h]


variable [DecidableEq α]

private lemma eliminateColLoopAux_eq
    (pivotRow : Fin m) (pivotCol : Fin n) (pivotVal : α) (r : Nat)
    (M : DenseMatrix m n α) (steps : List (RowOp m α))
    (hpivot : M.get pivotRow pivotCol = pivotVal) :
    eliminateColLoopAux pivotRow pivotCol pivotVal r M steps =
      eliminateColLoop pivotRow pivotCol r M steps := by
  simp [eliminateColLoop, hpivot]


/-- The helper function `eliminateColLoop` does not decrease the length of the steps list. -/
private theorem eliminateColLoop_steps_length_le (pivotRow : Fin m) (pivotCol : Fin n) (r : Nat)
    (M : DenseMatrix m n α) (steps : List (RowOp m α)) :
    (eliminateColLoop pivotRow pivotCol r M steps).2.length ≥ steps.length := by
  rw [eliminateColLoop, eliminateColLoopAux]
  split_ifs with hrow
  · simp only [ne_eq, List.concat_eq_append, ite_not, dite_eq_ite]
    split_ifs with hEq hcoeff
    · simpa [eliminateColLoopAux_eq (pivotRow := pivotRow) (pivotCol := pivotCol)
        (pivotVal := M.get pivotRow pivotCol) (r := r + 1) (M := M) (steps := steps) rfl] using
        eliminateColLoop_steps_length_le pivotRow pivotCol (r + 1) M steps
    · simpa [eliminateColLoopAux_eq (pivotRow := pivotRow) (pivotCol := pivotCol)
        (pivotVal := M.get pivotRow pivotCol) (r := r + 1) (M := M) (steps := steps) rfl] using
        eliminateColLoop_steps_length_le pivotRow pivotCol (r + 1) M steps
    · let i : Fin m := ⟨r, hrow⟩
      let M' := replaceRow M pivotRow i (-M.get i pivotCol / M.get pivotRow pivotCol)
      let steps' :=
        steps ++ [RowOp.replace pivotRow i (-M.get i pivotCol / M.get pivotRow pivotCol)]
      have huse : pivotRow ≠ i := by
        push Not at hEq
        exact hEq.symm
      have hpivot' : M'.get pivotRow pivotCol = M.get pivotRow pivotCol := by
        simp [M', replaceRow, huse, of_apply]
      have hrec :
          (eliminateColLoop pivotRow pivotCol (r + 1) M' steps').2.length ≥ steps'.length := by
        simpa [M', steps'] using
          eliminateColLoop_steps_length_le pivotRow pivotCol (r + 1) M' steps'
      have hrec' :
          (eliminateColLoopAux pivotRow pivotCol (M.get pivotRow pivotCol)
            (r + 1) M' steps').2.length ≥ steps'.length := by
        simpa [eliminateColLoopAux_eq (pivotRow := pivotRow) (pivotCol := pivotCol)
          (pivotVal := M.get pivotRow pivotCol) (r := r + 1) (M := M')
          (steps := steps') hpivot'] using hrec
      trans steps'.length
      · exact hrec'
      · aesop
  · simp

lemma eliminateColLoop_steps_prefix_length_le (pivotRow : Fin m) (pivotCol : Fin n) (r : Nat)
    (M : DenseMatrix m n α) (l1 l2 : List (RowOp m α)) :
    (eliminateColLoop pivotRow pivotCol r M (l1 ++ l2)).2.length ≥ l1.length := by
  trans (l1 ++ l2).length
  · exact eliminateColLoop_steps_length_le pivotRow pivotCol r M (l1 ++ l2)
  · aesop

lemma eliminateCol_steps_prefix_length_le
    (M : DenseMatrix m n α) (pivotRow : Fin m) (pivotCol : Fin n)
    (l1 l2 : List (RowOp m α)) (reduced : Bool) :
    (eliminateCol M pivotRow pivotCol (l1 ++ l2) reduced).2.length ≥ l1.length := by
  rw [eliminateCol]
  split_ifs
  · exact eliminateColLoop_steps_prefix_length_le pivotRow pivotCol 0 M l1 l2
  · exact eliminateColLoop_steps_prefix_length_le pivotRow pivotCol (↑pivotRow) M l1 l2

private theorem eliminateColLoopAux_steps_invertible
    (pr : Fin m) (pc : Fin n) (v : α) (r : Nat)
    (M : DenseMatrix m n α) (steps : List (RowOp m α))
    (hs : ∀ op ∈ steps, op.IsInvertible) :
    ∀ op ∈ (eliminateColLoopAux pr pc v r M steps).2, op.IsInvertible := by
  rw [eliminateColLoopAux]
  split
  · dsimp only
    split
    · exact eliminateColLoopAux_steps_invertible _ _ _ _ _ _ hs
    · rename_i hr hne
      split
      · apply eliminateColLoopAux_steps_invertible
        simpa only [List.concat_eq_append, List.forall_mem_append,
          List.mem_singleton, forall_eq, RowOp.IsInvertible] using And.intro hs (Ne.symm hne)
      · exact eliminateColLoopAux_steps_invertible _ _ _ _ _ _ hs
  · exact hs
termination_by m - r
decreasing_by all_goals omega

private theorem eliminateCol_steps_invertible
    (M : DenseMatrix m n α) (pr : Fin m) (pc : Fin n)
    (steps : List (RowOp m α)) (reduced : Bool)
    (hs : ∀ op ∈ steps, op.IsInvertible) :
    ∀ op ∈ (eliminateCol M pr pc steps reduced).2, op.IsInvertible := by
  unfold eliminateCol eliminateColLoop
  split <;> exact eliminateColLoopAux_steps_invertible _ _ _ _ _ _ hs

/-- Every newly emitted operation is invertible, provided the initial log is valid. -/
theorem rowReductionAux_steps_invertible
    (M : DenseMatrix m n α) (r c : Nat) (steps : List (RowOp m α)) (reduced : Bool)
    (hs : ∀ op ∈ steps, op.IsInvertible) :
    ∀ op ∈ (rowReductionAux M r c steps reduced).2, op.IsInvertible := by
  rw [rowReductionAux]
  split_ifs with hr hc
  · dsimp only
    split
    · exact hs
    · rename_i pr pc hp
      apply rowReductionAux_steps_invertible
      apply eliminateCol_steps_invertible
      have hpivot :
          (if pr.val = r then M else swapRow M ⟨r, hr⟩ pr).get ⟨r, hr⟩ pc ≠ 0 := by
        have hn := checkPivot_some_nonzero M r c hp
        by_cases he : pr.val = r
        · have he' : pr = ⟨r, hr⟩ := Fin.ext he
          simpa [he, he'] using hn
        · simpa [he, get_swapRow] using hn
      have hswap : ∀ op ∈ (if pr.val = r then steps else
          steps.concat (.swap ⟨r, hr⟩ pr)), op.IsInvertible := by
        split
        · exact hs
        · simpa only [List.concat_eq_append, List.forall_mem_append,
            List.mem_singleton, forall_eq, RowOp.IsInvertible, and_true] using hs
      split_ifs <;>
        simp_all only [List.concat_eq_append, List.forall_mem_append,
          List.mem_singleton, forall_eq, RowOp.IsInvertible, and_true,
          ite_true, ite_false, implies_true, true_and] <;> exact inv_ne_zero hpivot
  · exact hs
  · exact hs
termination_by m - r
decreasing_by all_goals omega

private theorem eliminateColLoop_replay
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
        rw [eliminateColLoop, eliminateColLoopAux, dite_eq_right (not_lt_of_ge hr)]
        simp
    | succ k ih =>
        intro r M steps hk
        have hr : r < m := by omega
        have hk' : m - (r + 1) = k := by omega
        let i : Fin m := ⟨r, hr⟩
        rw [eliminateColLoop, eliminateColLoopAux, dite_eq_left hr]
        by_cases hEq : i = pivotRow
        · obtain ⟨ops_tail, htail⟩ := ih (r + 1) M steps hk'
          exact ⟨ops_tail, by simpa [i, hEq, dite_eq_ite, eliminateColLoop] using htail⟩
        · by_cases hcoeff : M.get i pivotCol ≠ 0
          · let op : RowOp m α :=
              .replace pivotRow i (-M.get i pivotCol / M.get pivotRow pivotCol)
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
                  (pivotVal := M pivotRow pivotCol) (r := r + 1) (M := M)
                  (steps := steps) rfl] using htail⟩
  exact hrec (m - r) r M steps rfl

private theorem eliminateCol_replay
    (M : DenseMatrix m n α) (pivotRow : Fin m) (pivotCol : Fin n)
    (steps : List (RowOp m α)) (reduced : Bool) :
    ∃ ops_tail : List (RowOp m α),
      eliminateCol M pivotRow pivotCol steps reduced =
        (ops_tail.foldl applyRowOp M, steps ++ ops_tail) := by
  rw [eliminateCol]
  by_cases hred : reduced
  · simpa [hred] using eliminateColLoop_replay pivotRow pivotCol 0 M steps
  · simpa [hred] using eliminateColLoop_replay pivotRow pivotCol pivotRow.1 M steps

private theorem rowReductionAux_replay
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
        rw [rowReductionAux, dite_eq_left hr]
        by_cases hc : c < n
        · rw [ite_eq_left hc]
          cases hcp : checkPivot M r c with
          | none =>
              refine ⟨[], ?_⟩
              simp
          | some p =>
              rcases p with ⟨pivotRow, pivotCol⟩
              let rowFin : Fin m := ⟨r, hr⟩
              let swapOp : RowOp m α := .swap rowFin pivotRow
              let swapOps : List (RowOp m α) :=
                if pivotRow.1 = r then [] else [swapOp]
              let steps1 : List (RowOp m α) := steps ++ swapOps
              have hsteps1 : steps1 = if pivotRow.1 = r then steps else steps ++ [swapOp] := by
                by_cases hswap : pivotRow.1 = r <;> simp [steps1, swapOps, hswap]
              let m1 : DenseMatrix m n α :=
                if pivotRow.1 = r then M else swapRow M rowFin pivotRow
              have hm1 : m1 = swapOps.foldl applyRowOp M := by
                by_cases hswap : pivotRow.1 = r
                · have hpiv : pivotRow = rowFin := by
                    ext
                    simpa [rowFin] using hswap
                  subst hpiv
                  simp [m1, swapOps, rowFin]
                · simp [m1, swapOp, swapOps, applyRowOp, hswap]
              let pivotVal : α := m1.get rowFin pivotCol
              let scaleOp : RowOp m α := .scale rowFin pivotVal⁻¹
              cases hred : reduced with
              | false =>
                  obtain ⟨ops_elim, hElim⟩ :=
                    eliminateCol_replay m1 rowFin pivotCol steps1 false
                  obtain ⟨ops_rec, hRec⟩ :=
                    ih (ops_elim.foldl applyRowOp m1) (r + 1) (c + 1) (steps1 ++ ops_elim) false hk'
                  refine ⟨swapOps ++ ops_elim ++ ops_rec, ?_⟩
                  have hbranch :
                      (match eliminateCol m1 rowFin pivotCol steps1 false with
                        | (m3, steps3) => rowReductionAux m3 (r + 1) (c + 1) steps3 false) =
                        (ops_rec.foldl applyRowOp (ops_elim.foldl applyRowOp m1),
                          steps1 ++ ops_elim ++ ops_rec) := by
                    simpa [hElim] using hRec
                  have hfinal :
                      (ops_rec.foldl applyRowOp (ops_elim.foldl applyRowOp m1),
                        steps1 ++ ops_elim ++ ops_rec) =
                        (List.foldl applyRowOp M (swapOps ++ ops_elim ++ ops_rec),
                          steps ++ (swapOps ++ ops_elim ++ ops_rec)) := by
                    apply Prod.ext
                    · simp only [List.foldl_append]
                      rw [hm1]
                    · simp [steps1, List.append_assoc]
                  simpa [hcp, rowFin, hred, hsteps1, swapOps, steps1, m1, pivotVal,
                    List.concat_eq_append] using
                    hbranch.trans hfinal
              | true =>
                  by_cases hpv : pivotVal = 1
                  · obtain ⟨ops_elim, hElim⟩ :=
                      eliminateCol_replay m1 rowFin pivotCol steps1 true
                    obtain ⟨ops_rec, hRec⟩ :=
                      ih (ops_elim.foldl applyRowOp m1) (r + 1) (c + 1) (steps1 ++ ops_elim)
                        true hk'
                    refine ⟨swapOps ++ ops_elim ++ ops_rec, ?_⟩
                    have hbranch :
                        (match eliminateCol m1 rowFin pivotCol steps1 true with
                          | (m3, steps3) => rowReductionAux m3 (r + 1) (c + 1) steps3 true) =
                          (ops_rec.foldl applyRowOp (ops_elim.foldl applyRowOp m1),
                            steps1 ++ ops_elim ++ ops_rec) := by
                      simpa [hElim] using hRec
                    have hfinal :
                        (ops_rec.foldl applyRowOp (ops_elim.foldl applyRowOp m1),
                          steps1 ++ ops_elim ++ ops_rec) =
                          (List.foldl applyRowOp M (swapOps ++ ops_elim ++ ops_rec),
                            steps ++ (swapOps ++ ops_elim ++ ops_rec)) := by
                      apply Prod.ext
                      · simp only [List.foldl_append]
                        rw [hm1]
                      · simp [steps1, List.append_assoc]
                    simpa [hcp, rowFin, hred, hpv, hsteps1, swapOps, steps1, m1, pivotVal,
                      List.concat_eq_append]
                      using hbranch.trans hfinal
                  · let steps2 : List (RowOp m α) := steps1 ++ [scaleOp]
                    have hsteps2 : steps2 =
                        (if pivotRow.1 = r then steps else steps ++ [swapOp]) ++ [scaleOp] := by
                      change steps1 ++ [scaleOp] =
                        (if pivotRow.1 = r then steps else steps ++ [swapOp]) ++ [scaleOp]
                      rw [hsteps1]
                    let m2 : DenseMatrix m n α := scaleRow m1 rowFin pivotVal⁻¹
                    have hm2 : m2 = applyRowOp m1 scaleOp := by
                      simp [m2, scaleOp, applyRowOp]
                    obtain ⟨ops_elim, hElim⟩ :=
                      eliminateCol_replay m2 rowFin pivotCol steps2 true
                    obtain ⟨ops_rec, hRec⟩ :=
                      ih (ops_elim.foldl applyRowOp m2) (r + 1) (c + 1) (steps2 ++ ops_elim)
                        true hk'
                    refine ⟨(swapOps ++ [scaleOp]) ++ ops_elim ++ ops_rec, ?_⟩
                    have hbranch :
                        (match eliminateCol m2 rowFin pivotCol steps2 true with
                          | (m3, steps3) => rowReductionAux m3 (r + 1) (c + 1) steps3 true) =
                          (ops_rec.foldl applyRowOp (ops_elim.foldl applyRowOp m2),
                            steps2 ++ ops_elim ++ ops_rec) := by
                      simpa [hElim] using hRec
                    have hfinal :
                        (ops_rec.foldl applyRowOp (ops_elim.foldl applyRowOp m2),
                          steps2 ++ ops_elim ++ ops_rec) =
                          (List.foldl applyRowOp M ((swapOps ++ [scaleOp]) ++ ops_elim ++ ops_rec),
                            steps ++ ((swapOps ++ [scaleOp]) ++ ops_elim ++ ops_rec)) := by
                      apply Prod.ext
                      · simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
                        rw [hm2, hm1]
                      · simp [steps1, steps2, List.append_assoc]
                    simpa [hcp, rowFin, hred, hpv, hsteps1, hsteps2, swapOps, steps1,
                      m1, pivotVal, scaleOp, steps2, m2, List.concat_eq_append] using
                      hbranch.trans hfinal
        · refine ⟨[], ?_⟩
          simp [hc]
  exact hrec (m - r) M r c steps reduced rfl

theorem rowReductionAux_steps_length_le (M : DenseMatrix m n α) (r c : Nat)
    (steps : List (RowOp m α)) (reduced : Bool) :
    (rowReductionAux M r c steps reduced).2.length >= steps.length := by
  obtain ⟨ops_tail, hlog⟩ := rowReductionAux_replay M r c steps reduced
  rw [hlog]
  simp

/--
If the `steps` certificate is empty, then the resulting matrix is the same as the source
matrix.
-/
lemma rowReductionAux_source_eq_result_of_empty_steps (M M' : DenseMatrix m n α) (r c : Nat)
    (ops : List (RowOp m α)) (reduced : Bool)
    : rowReductionAux M r c ops reduced = (M', []) → M = M' := by
  intro h
  obtain ⟨ops_tail, hlog⟩ := rowReductionAux_replay M r c ops reduced
  rw [hlog] at h
  injection h with hM hOps
  have hnil : ops_tail = [] := (List.eq_nil_of_append_eq_nil hOps).2
  simpa [hnil] using hM

theorem rowReductionAux_replay_steps (M M' : DenseMatrix m n α) (r c : Nat)
    (ops_head ops_tail ops_final : List (RowOp m α)) (reduced : Bool)
    (h_ops : ops_final = ops_head ++ ops_tail)
    : rowReductionAux M r c ops_head reduced = (M', ops_head ++ ops_tail) →
        ops_tail.foldl applyRowOp M = M' := by
  intro h
  have h' : rowReductionAux M r c ops_head reduced = (M', ops_final) := by
    simpa [h_ops] using h
  obtain ⟨ops_tail', hlog⟩ := rowReductionAux_replay M r c ops_head reduced
  rw [hlog] at h'
  injection h' with hM hOps
  have hOps' : ops_head ++ ops_tail' = ops_head ++ ops_tail := by
    simpa [h_ops] using hOps
  have htail : ops_tail' = ops_tail := (List.append_right_inj ops_head).mp hOps'
  simpa [htail] using hM

private theorem rowEchelonForm_replay_steps_of_eq
    (M M' : DenseMatrix m n α) (ops : List (RowOp m α))
    : rowEchelonForm M = { matrix := M', steps := ops } → ops.foldl applyRowOp M = M' := by
  intro h
  have h_ops : ops = [] ++ ops := by simp
  have h' : rowReductionAux M 0 0 [] false = (M', [] ++ ops) := by
    simp only [List.nil_append]
    unfold rowEchelonForm at h
    injection h with h_matrix h_steps
    rw [← h_matrix, ← h_steps]
  simpa using rowReductionAux_replay_steps M M' 0 0 [] ops ops false h_ops h'

private theorem reducedRowEchelonForm_replay_steps_of_eq (M M' : DenseMatrix m n α)
    (ops : List (RowOp m α))
    : reducedRowEchelonForm M = { matrix := M', steps := ops } → ops.foldl applyRowOp M = M' := by
  intro h
  have h_ops : ops = [] ++ ops := by simp
  have h' : rowReductionAux M 0 0 [] true = (M', [] ++ ops) := by
    simp only [List.nil_append]
    unfold reducedRowEchelonForm at h
    injection h with h_matrix h_steps
    rw [← h_matrix, ← h_steps]
  simpa using rowReductionAux_replay_steps M M' 0 0 [] ops ops true h_ops h'

/-- Applying the `RowOps` in the certificate to the source matrix returns the resulting matrix. -/
theorem rowEchelonForm_replay_steps
    (M : DenseMatrix m n α) :
    (rowEchelonForm M).steps.foldl applyRowOp M = (rowEchelonForm M).matrix := by
  simpa [rowEchelonForm] using
    (rowEchelonForm_replay_steps_of_eq
      (M := M)
      (M' := (rowEchelonForm M).1)
      (ops := (rowEchelonForm M).2)
      rfl)

theorem reducedRowEchelonForm_replay_steps
    (M : DenseMatrix m n α) :
    (reducedRowEchelonForm M).steps.foldl applyRowOp M =
      (reducedRowEchelonForm M).matrix := by
  simpa [reducedRowEchelonForm] using
    (reducedRowEchelonForm_replay_steps_of_eq
      (M := M)
      (M' := (reducedRowEchelonForm M).1)
      (ops := (reducedRowEchelonForm M).2)
      rfl)

omit [DecidableEq α] in
/-- Replaying a list of invertible row operations preserves row equivalence. -/
theorem rowEquivalent_foldl_applyRowOp (M : DenseMatrix m n α)
    (ops : List (RowOp m α)) (hops : ∀ op ∈ ops, op.IsInvertible) :
    Matrix.RowEquivalent M.toMatrix (ops.foldl applyRowOp M).toMatrix := by
  induction ops generalizing M with
  | nil => exact Matrix.RowEquivalent.refl _
  | cons op ops ih =>
      exact (op.rowEquivalent_toMatrix (hops op (by simp)) M).trans
        (ih (applyRowOp M op) (fun op hop => hops op (List.mem_cons_of_mem _ hop)))

/-- Every operation in the row-echelon certificate is invertible. -/
theorem rowEchelonForm_steps_invertible (M : DenseMatrix m n α) :
    ∀ op ∈ (rowEchelonForm M).steps, op.IsInvertible :=
  rowReductionAux_steps_invertible M 0 0 [] false (by simp)

/-- Every operation in the reduced-row-echelon certificate is invertible. -/
theorem reducedRowEchelonForm_steps_invertible (M : DenseMatrix m n α) :
    ∀ op ∈ (reducedRowEchelonForm M).steps, op.IsInvertible :=
  rowReductionAux_steps_invertible M 0 0 [] true (by simp)

/-- The row-echelon output is row equivalent to the input, as witnessed by its certificate. -/
theorem rowEchelonForm_rowEquivalent (M : DenseMatrix m n α) :
    Matrix.RowEquivalent M.toMatrix (rowEchelonForm M).matrix.toMatrix := by
  have h := rowEquivalent_foldl_applyRowOp M _ (rowEchelonForm_steps_invertible M)
  rwa [rowEchelonForm_replay_steps] at h

/-- The reduced-row-echelon output is row equivalent to the input, via its certificate. -/
theorem reducedRowEchelonForm_rowEquivalent (M : DenseMatrix m n α) :
    Matrix.RowEquivalent M.toMatrix (reducedRowEchelonForm M).matrix.toMatrix := by
  have h := rowEquivalent_foldl_applyRowOp M _ (reducedRowEchelonForm_steps_invertible M)
  rwa [reducedRowEchelonForm_replay_steps] at h

/-- Row reduction preserves the homogeneous solution set. -/
theorem rowEchelonForm_mulVec_eq_zero_iff (M : DenseMatrix m n α) (x : Fin n → α) :
    (rowEchelonForm M).matrix.toMatrix *ᵥ x = 0 ↔ M.toMatrix *ᵥ x = 0 :=
  ((rowEchelonForm_rowEquivalent M).mul_eq_zero_iff x).symm

/-- Reduced row reduction preserves the homogeneous solution set. -/
theorem reducedRowEchelonForm_mulVec_eq_zero_iff (M : DenseMatrix m n α) (x : Fin n → α) :
    (reducedRowEchelonForm M).matrix.toMatrix *ᵥ x = 0 ↔ M.toMatrix *ᵥ x = 0 :=
  ((reducedRowEchelonForm_rowEquivalent M).mul_eq_zero_iff x).symm

/-! ## Echelon-form invariants

Completed rows have a leading entry, zeros below it (including earlier columns),
and, in reduced mode, a unit pivot with zeros above it. The remaining rows are
zero to the left of the search column. These are loop invariants, expressed using
mathlib's `IsLeadingEntry`; the public conclusions use mathlib's echelon predicates.
-/

private def CompletedRow (M : DenseMatrix m n α) (reduced : Bool)
    (i : Fin m) (p : Fin n) : Prop :=
  M.toMatrix.IsLeadingEntry i p ∧
  (∀ k : Fin m, i < k → ∀ j : Fin n, j ≤ p → M.get k j = 0) ∧
  (reduced = true → M.get i p = 1 ∧ ∀ k : Fin m, k < i → M.get k p = 0)

private structure EchelonProgress (M : DenseMatrix m n α) (r c : Nat)
    (reduced : Bool) : Prop where
  left_zero : ∀ i : Fin m, r ≤ i.val → ∀ j : Fin n, j.val < c → M.get i j = 0
  completed : ∀ i : Fin m, i.val < r → ∃ p, CompletedRow M reduced i p

omit [DecidableEq α] in
private lemma CompletedRow.congr_columns {M N : DenseMatrix m n α} {reduced : Bool}
    {i : Fin m} {p : Fin n} (h : CompletedRow M reduced i p)
    (he : ∀ k j, j ≤ p → N.get k j = M.get k j) : CompletedRow N reduced i p := by
  rcases h with ⟨hlead, hbelow, hred⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro j hj
    change N.get i j = 0
    rw [he i j (le_of_lt hj)]
    exact hlead.1 j hj
  · change N.get i p ≠ 0
    rw [he i p le_rfl]
    exact hlead.2
  · intro k hk j hj
    rw [he k j hj]
    exact hbelow k hk j hj
  · intro hr
    obtain ⟨hp, hz⟩ := hred hr
    exact ⟨(he i p le_rfl).trans hp, fun k hk => (he k p le_rfl).trans (hz k hk)⟩

omit [DecidableEq α] in
private lemma EchelonProgress.finish {M : DenseMatrix m n α} {r c : Nat}
    {reduced : Bool} (h : EchelonProgress M r c reduced)
    (hz : ∀ i : Fin m, r ≤ i.val → ∀ j, M.get i j = 0) :
    M.toMatrix.IsRowEchelon ∧ (reduced = true → M.toMatrix.IsReducedRowEchelon) := by
  have he : M.toMatrix.IsRowEchelon := by
    intro i k hik j hleft
    by_cases hk : k.val < r
    · obtain ⟨p, hp, hb, _⟩ := h.completed i (lt_trans hik hk)
      have hj : j ≤ p := by
        by_contra hn
        exact hp.2 (hleft p (lt_of_not_ge hn))
      exact hb k hik j hj
    · exact hz k (Nat.le_of_not_gt hk) j
  refine ⟨he, fun hr => ⟨he, ?_, ?_⟩⟩
  · intro i p hp
    have hi : i.val < r := by
      by_contra hn
      exact hp.2 (hz i (Nat.le_of_not_gt hn) p)
    obtain ⟨q, hq, _, hred⟩ := h.completed i hi
    have heq := hp.unique hq
    subst p
    exact (hred hr).1
  · intro k i p hki hp
    have hi : i.val < r := by
      by_contra hn
      exact hp.2 (hz i (Nat.le_of_not_gt hn) p)
    obtain ⟨q, hq, _, hred⟩ := h.completed i hi
    have heq := hp.unique hq
    subst p
    exact (hred hr).2 k hki

omit [DecidableEq α] in
private lemma EchelonProgress.swap {M : DenseMatrix m n α} {r c : Nat}
    {reduced : Bool} (h : EchelonProgress M r c reduced)
    (a b : Fin m) (ha : r ≤ a.val) (hb : r ≤ b.val) :
    EchelonProgress (swapRow M a b) r c reduced := by
  constructor
  · intro i hi j hj
    simp only [get_swapRow]
    split_ifs <;> apply h.left_zero _ (by omega) j hj
  · intro i hi
    obtain ⟨p, hp⟩ := h.completed i hi
    refine ⟨p, hp.congr_columns ?_⟩
    intro k j hj
    have hza := hp.2.1 a (by omega) j hj
    have hzb := hp.2.1 b (by omega) j hj
    simp only [get_swapRow]
    split_ifs <;> subst_vars <;> simp_all

omit [DecidableEq α] in
private lemma EchelonProgress.scale {M : DenseMatrix m n α} {r c : Nat}
    {reduced : Bool} (h : EchelonProgress M r c reduced)
    (a : Fin m) (ha : r ≤ a.val) (v : α) :
    EchelonProgress (scaleRow M a v) r c reduced := by
  constructor
  · intro i hi j hj
    simp [get_scaleRow, h.left_zero i hi j hj]
  · intro i hi
    obtain ⟨p, hp⟩ := h.completed i hi
    refine ⟨p, hp.congr_columns ?_⟩
    intro k j hj
    have hza := hp.2.1 a (by omega) j hj
    by_cases hk : k = a
    · subst k
      simp [hza]
    · simp [hk]

private lemma EchelonProgress.eliminate {M : DenseMatrix m n α} {r c : Nat}
    {reduced : Bool} (h : EchelonProgress M r c reduced)
    (hr : r < m) (p : Fin n) (hcp : c ≤ p.val)
    (hn : M.get ⟨r, hr⟩ p ≠ 0)
    (hz : ∀ k : Fin m, r ≤ k.val → ∀ j : Fin n, j < p → M.get k j = 0)
    (hone : reduced = true → M.get ⟨r, hr⟩ p = 1)
    (steps : List (RowOp m α)) :
    EchelonProgress (eliminateCol M ⟨r, hr⟩ p steps reduced).1 (r + 1) (c + 1) reduced := by
  let N := (eliminateCol M ⟨r, hr⟩ p steps reduced).1
  have hcol (j : Fin n) (hj : M.get ⟨r, hr⟩ j = 0) (i : Fin m) :
      N.get i j = M.get i j := by
    cases reduced <;>
      exact eliminateCol_go_preserves_col M ⟨r, hr⟩ p _ steps j hj i
  have hrow (j : Fin n) : N.get ⟨r, hr⟩ j = M.get ⟨r, hr⟩ j := by
    cases reduced <;> exact eliminateCol_go_pivotRow M ⟨r, hr⟩ p steps _ j
  have hbelow (i : Fin m) (hi : r < i.val) : N.get i p = 0 := by
    cases he : reduced
    · dsimp [N]
      rw [he, eliminateCol_matrix_irrel_false]
      exact eliminateCol_below_pivotCol_zero M ⟨r, hr⟩ p hn i hi
    · dsimp [N]
      rw [he, eliminateCol_matrix_irrel]
      exact eliminateCol_pivotCol_zero M ⟨r, hr⟩ p (hone he) i (by
        intro e
        have := congrArg Fin.val e
        change i.val = r at this
        omega)
  have hzeros (i : Fin m) (hi : r < i.val) (j : Fin n) (hj : j ≤ p) : N.get i j = 0 := by
    rcases lt_or_eq_of_le hj with hj | rfl
    · rw [hcol j (hz ⟨r, hr⟩ le_rfl j hj) i]
      exact hz i (Nat.le_of_lt hi) j hj
    · exact hbelow i hi
  constructor
  · intro i hi j hj
    exact hzeros i (by omega) j (by omega)
  · intro i hi
    by_cases hir : i.val < r
    · obtain ⟨q, hq⟩ := h.completed i hir
      refine ⟨q, hq.congr_columns ?_⟩
      intro k j hj
      exact hcol j (hq.2.1 ⟨r, hr⟩ hir j hj) k
    · have hie : i = ⟨r, hr⟩ := by
        apply Fin.ext
        change i.val = r
        omega
      subst i
      refine ⟨p, ⟨?_, ?_⟩, ?_, ?_⟩
      · intro j hj
        change N.get ⟨r, hr⟩ j = 0
        rw [hrow]
        exact hz ⟨r, hr⟩ le_rfl j hj
      · change N.get ⟨r, hr⟩ p ≠ 0
        rwa [hrow]
      · exact fun k hk j hj => hzeros k hk j hj
      · intro he
        refine ⟨(hrow p).trans (hone he), ?_⟩
        intro k hk
        rw [he, eliminateCol_matrix_irrel]
        exact eliminateCol_pivotCol_zero M ⟨r, hr⟩ p (hone he) k (ne_of_lt hk)

private theorem rowReductionAux_forms
    (M : DenseMatrix m n α) (r c : Nat) (steps : List (RowOp m α)) (reduced : Bool)
    (h : EchelonProgress M r c reduced) :
    (rowReductionAux M r c steps reduced).1.toMatrix.IsRowEchelon ∧
    (reduced = true → (rowReductionAux M r c steps reduced).1.toMatrix.IsReducedRowEchelon) := by
  rw [rowReductionAux]
  split_ifs with hr hc
  · dsimp only
    split
    · rename_i hp
      apply h.finish
      intro i hi j
      by_cases hj : j.val < c
      · exact h.left_zero i hi j hj
      · exact checkPivot_none_zero M r c hp j (Nat.le_of_not_gt hj) i hi
    · rename_i pr pc hp
      have hpr : r ≤ pr.val := checkPivot_some_row_ge M r c hp
      have hnon := checkPivot_some_nonzero M r c hp
      have hpc : c ≤ pc.val := by
        by_contra hn
        exact hnon (h.left_zero pr hpr pc (Nat.lt_of_not_ge hn))
      have hz : ∀ i : Fin m, r ≤ i.val → ∀ j : Fin n, j < pc → M.get i j = 0 := by
        intro i hi j hj
        by_cases hjc : j.val < c
        · exact h.left_zero i hi j hjc
        · exact checkPivot_some_minimal M r c hp j (Nat.le_of_not_gt hjc) hj i hi
      let S := if pr.val = r then M else swapRow M ⟨r, hr⟩ pr
      have hs : EchelonProgress S r c reduced := by
        dsimp only [S]
        split
        · exact h
        · exact h.swap ⟨r, hr⟩ pr le_rfl hpr
      have hzs : ∀ i : Fin m, r ≤ i.val → ∀ j : Fin n, j < pc → S.get i j = 0 := by
        intro i hi j hj
        dsimp only [S]
        split
        · exact hz i hi j hj
        · simp only [get_swapRow]
          split_ifs
          · exact hz pr hpr j hj
          · exact hz ⟨r, hr⟩ le_rfl j hj
          · exact hz i hi j hj
      have hns : S.get ⟨r, hr⟩ pc ≠ 0 := by
        dsimp only [S]
        split
        · rename_i he
          have he' : pr = ⟨r, hr⟩ := Fin.ext he
          simpa [he'] using hnon
        · simpa using hnon
      let T := if !reduced || S.get ⟨r, hr⟩ pc = 1 then S
        else scaleRow S ⟨r, hr⟩ (S.get ⟨r, hr⟩ pc)⁻¹
      have ht : EchelonProgress T r c reduced := by
        dsimp only [T]
        split
        · exact hs
        · exact hs.scale ⟨r, hr⟩ le_rfl _
      have hzt : ∀ i : Fin m, r ≤ i.val → ∀ j : Fin n, j < pc → T.get i j = 0 := by
        intro i hi j hj
        dsimp only [T]
        split
        · exact hzs i hi j hj
        · simp [get_scaleRow, hzs i hi j hj]
      have hnt : T.get ⟨r, hr⟩ pc ≠ 0 := by
        dsimp only [T]
        split
        · exact hns
        · simp [get_scaleRow, inv_mul_cancel₀ hns]
      have hot : reduced = true → T.get ⟨r, hr⟩ pc = 1 := by
        intro he
        dsimp only [T]
        split
        · rename_i hg
          simpa [he] using hg
        · simp [get_scaleRow, inv_mul_cancel₀ hns]
      apply rowReductionAux_forms
      exact ht.eliminate hr pc hpc hnt hzt hot _
  · apply h.finish
    intro i hi j
    exact h.left_zero i hi j (by omega)
  · apply h.finish
    intro i hi
    omega
termination_by m - r
decreasing_by all_goals omega

/-- The executable row-echelon routine returns a matrix in mathlib's row-echelon form. -/
theorem rowEchelonForm_isRowEchelon (M : DenseMatrix m n α) :
    (rowEchelonForm M).matrix.toMatrix.IsRowEchelon :=
  (rowReductionAux_forms M 0 0 [] false ⟨by omega, by omega⟩).1

/-- The executable reduced-row-echelon routine satisfies mathlib's reduced-form predicate. -/
theorem reducedRowEchelonForm_isReducedRowEchelon (M : DenseMatrix m n α) :
    (reducedRowEchelonForm M).matrix.toMatrix.IsReducedRowEchelon :=
  (rowReductionAux_forms M 0 0 [] true ⟨by omega, by omega⟩).2 rfl

/-- The computed row-echelon matrix is a representative of the source matrix. -/
theorem rowEchelonForm_isRowEchelonOf (M : DenseMatrix m n α) :
    (rowEchelonForm M).matrix.toMatrix.IsRowEchelonOf M.toMatrix :=
  ⟨(rowEchelonForm_rowEquivalent M).symm, rowEchelonForm_isRowEchelon M⟩

/-- The computed reduced-row-echelon matrix is a representative of the source matrix. -/
theorem reducedRowEchelonForm_isReducedRowEchelonOf (M : DenseMatrix m n α) :
    (reducedRowEchelonForm M).matrix.toMatrix.IsReducedRowEchelonOf M.toMatrix :=
  ⟨(reducedRowEchelonForm_rowEquivalent M).symm,
    reducedRowEchelonForm_isReducedRowEchelon M⟩

end DenseMatrix
