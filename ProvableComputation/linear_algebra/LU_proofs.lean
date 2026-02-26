import ProvableComputation.linear_algebra.LUFactorization
import ProvableComputation.linear_algebra.rref_proofs

variable {R : Type} [Field R] [DecidableEq R]
<<<<<<< Updated upstream
variable {a : ℕ}
variable {ha : a > 0}

def unfoldBuildPL (steps : List (RowOp a R)) (M₁ M₂ M P L U : squareMatrix a R)
    (h1 : rowEchelonForm M = (U, steps))
    : buildPL steps M₁ M₂ = (P, L) → P * L * U = M := by
  intro h2
  unfold buildPL at h2
  split at h2
  · rename_i steps
    rcases h2
    rw [rowEchelonForm] at h1
    rw [rrefAux] at h1
    split_ifs at h1 with h3
    · aesop
      · have M_eq_zero : M = 0 := by
          ext i j
          have h' : ∀ c : Fin a, 0 ≤ c.1 → ∀ r : Fin a, 0 ≤ r.1 → M r c = 0 := by
            exact Matrix.checkPivot_none_zero M 0 0 heq
          apply h'
          · exact Nat.zero_le ↑j
          · exact Nat.zero_le ↑i
        rw [M_eq_zero]
        simp
      · let res := eliminateCol M ⟨0, h3⟩ pivotCol
          [RowOp.swap ⟨0, h3⟩ pivotRow, RowOp.factor ⟨0, h3⟩ 1] false
        have hlen : ([] : List (RowOp a R)).length ≥ res.2.length := by
          have h' : (rrefAux res.1 1 1 res.2 false).2 = [] := by
            rw [h1]
          rw [← h']
          apply row_reduction_adds_steps res.1 1 1 res.2 false
        unfold res at hlen
        have h_elim : (eliminateCol M ⟨0, h3⟩ pivotCol
            ([RowOp.swap ⟨0, h3⟩ pivotRow, RowOp.factor ⟨0, h3⟩ 1] ++ []) false).2.length
            ≥ [RowOp.swap ⟨0, h3⟩ pivotRow, RowOp.factor ⟨0, h3⟩ 1].length := by
          exact elim_col_adds_steps M ⟨0, h3⟩ pivotCol
            [RowOp.swap ⟨0, h3⟩ pivotRow, RowOp.factor ⟨0, h3⟩ 1] [] false
        aesop
      · let res := eliminateCol (factor M ⟨0, h3⟩ (M ⟨0, h3⟩ pivotCol)⁻¹) ⟨0, h3⟩ pivotCol
            [RowOp.swap ⟨0, h3⟩ pivotRow, RowOp.factor ⟨0, h3⟩ (M ⟨0, h3⟩ pivotCol)⁻¹] false
        have hlen : ([] : List (RowOp a R)).length ≥ res.2.length := by
          have h' : (rrefAux res.1 1 1 res.2 false).2 = [] := by
            rw [h1]
          rw [← h']
          apply row_reduction_adds_steps res.1 1 1 res.2 false
        unfold res at hlen
        have h_elim : (eliminateCol (factor M ⟨0, h3⟩ (M ⟨0, h3⟩ pivotCol)⁻¹) ⟨0, h3⟩ pivotCol
            [RowOp.swap ⟨0, h3⟩ pivotRow,
            RowOp.factor ⟨0, h3⟩ (M ⟨0, h3⟩ pivotCol)⁻¹] false).2.length
            ≥ [RowOp.swap ⟨0, h3⟩ pivotRow, RowOp.factor ⟨0, h3⟩ 1].length := by
          exact elim_col_adds_steps (factor M ⟨0, h3⟩ (M ⟨0, h3⟩ pivotCol)⁻¹) ⟨0, h3⟩ pivotCol
            [RowOp.swap ⟨0, h3⟩ pivotRow, RowOp.factor ⟨0, h3⟩ (M ⟨0, h3⟩ pivotCol)⁻¹] [] false
        aesop
      · let res := eliminateCol (swapRow M ⟨0, h3⟩ pivotRow) ⟨0, h3⟩ pivotCol
          [RowOp.swap ⟨0, h3⟩ pivotRow, RowOp.factor ⟨0, h3⟩ 1] false
        have hlen : ([] : List (RowOp a R)).length ≥ res.2.length := by
          have h' : (rrefAux res.1 1 1 res.2 false).2 = [] := by
            rw [h1]
          rw [← h']
          apply row_reduction_adds_steps res.1 1 1 res.2 false
        unfold res at hlen
        have h_elim : (eliminateCol (swapRow M ⟨0, h3⟩ pivotRow) ⟨0, h3⟩ pivotCol
          [RowOp.swap ⟨0, h3⟩ pivotRow, RowOp.factor ⟨0, h3⟩ 1] false).2.length
            ≥ [RowOp.swap ⟨0, h3⟩ pivotRow, RowOp.factor ⟨0, h3⟩ 1].length := by
          exact elim_col_adds_steps (swapRow M ⟨0, h3⟩ pivotRow) ⟨0, h3⟩ pivotCol
            [RowOp.swap ⟨0, h3⟩ pivotRow, RowOp.factor ⟨0, h3⟩ 1] [] false
        aesop
      · let res := eliminateCol (factor (swapRow M ⟨0, h3⟩ pivotRow) ⟨0, h3⟩
          (swapRow M ⟨0, h3⟩ pivotRow ⟨0, h3⟩ pivotCol)⁻¹) ⟨0, h3⟩ pivotCol
          [RowOp.swap ⟨0, h3⟩ pivotRow,
          RowOp.factor ⟨0, h3⟩ (swapRow M ⟨0, h3⟩ pivotRow ⟨0, h3⟩ pivotCol)⁻¹] false
        have hlen : ([] : List (RowOp a R)).length ≥ res.2.length := by
          have h' : (rrefAux res.1 1 1 res.2 false).2 = [] := by
            rw [h1]
          rw [← h']
          apply row_reduction_adds_steps res.1 1 1 res.2 false
        unfold res at hlen
        have h_elim : (eliminateCol (factor (swapRow M ⟨0, h3⟩ pivotRow) ⟨0, h3⟩
          (swapRow M ⟨0, h3⟩ pivotRow ⟨0, h3⟩ pivotCol)⁻¹) ⟨0, h3⟩ pivotCol
          [RowOp.swap ⟨0, h3⟩ pivotRow,
          RowOp.factor ⟨0, h3⟩ (swapRow M ⟨0, h3⟩ pivotRow ⟨0, h3⟩ pivotCol)⁻¹] false).2.length
            ≥ [RowOp.swap ⟨0, h3⟩ pivotRow, RowOp.factor ⟨0, h3⟩ 1].length := by
          exact elim_col_adds_steps (factor (swapRow M ⟨0, h3⟩ pivotRow) ⟨0, h3⟩
            (swapRow M ⟨0, h3⟩ pivotRow ⟨0, h3⟩ pivotCol)⁻¹) ⟨0, h3⟩ pivotCol
            [RowOp.swap ⟨0, h3⟩ pivotRow,
            RowOp.factor ⟨0, h3⟩ (swapRow M ⟨0, h3⟩ pivotRow ⟨0, h3⟩ pivotCol)⁻¹] [] false
        aesop
    · contradiction
  · rename_i ops
    aesop
    -- Need to find decreasing measure, e.g. find a way to use `ops` instead of `op :: ops`
    · apply unfoldBuildPL (RowOp.swap a_2 a_3 :: ops) M₁ M₂ M P L U h1
      exact h2
    · apply unfoldBuildPL (RowOp.factor row scale :: ops) M₁ M₂ M P L U h1
      exact h2
    · apply unfoldBuildPL (RowOp.replace use toReplace scale :: ops) M₁ M₂ M P L U h1
      exact h2
=======
variable {a : ℕ} [Nonempty (Fin a)]

lemma unfoldSteps (step : RowOp a R) (steps : List (RowOp a R)) (M U : squareMatrix a R)
    (h : rowEchelonForm M = (U, step :: steps))
    : rowEchelonForm ((Matrix.elementaryMatrixOfRowOp step) * M) = (U, steps) := by
  sorry

-- def unfoldBuildPL (steps : List (RowOp a R)) (M₁ M₂ M P L U : squareMatrix a R)
--     (h1 : rowEchelonForm M = (U, steps))
--     : buildPL steps M₁ M₂ = (P, L) → P * L * U = M := by
--   intro h2
--   unfold buildPL at h2
--   split at h2
--   · rename_i steps
--     rcases h2
--     rw [rowEchelonForm] at h1
--     rw [rrefAux] at h1
--     split_ifs at h1 with h3
--     · aesop
--       · have M_eq_zero : M = 0 := by
--           ext i j
--           have h' : ∀ c : Fin a, 0 ≤ c.1 → ∀ r : Fin a, 0 ≤ r.1 → M r c = 0 := by
--             exact Matrix.checkPivot_none_zero M 0 0 heq
--           apply h'
--           · exact Nat.zero_le ↑j
--           · exact Nat.zero_le ↑i
--         rw [M_eq_zero]
--         simp
--       · let res := eliminateCol M ⟨0, h3⟩ pivotCol
--           [RowOp.swap ⟨0, h3⟩ pivotRow, RowOp.factor ⟨0, h3⟩ 1] false
--         have hlen : ([] : List (RowOp a R)).length ≥ res.2.length := by
--           have h' : (rrefAux res.1 1 1 res.2 false).2 = [] := by
--             rw [h1]
--           rw [← h']
--           apply row_reduction_adds_steps res.1 1 1 res.2 false
--         unfold res at hlen
--         have h_elim : (eliminateCol M ⟨0, h3⟩ pivotCol
--             ([RowOp.swap ⟨0, h3⟩ pivotRow, RowOp.factor ⟨0, h3⟩ 1] ++ []) false).2.length
--             ≥ [RowOp.swap ⟨0, h3⟩ pivotRow, RowOp.factor ⟨0, h3⟩ 1].length := by
--           exact elim_col_adds_steps M ⟨0, h3⟩ pivotCol
--             [RowOp.swap ⟨0, h3⟩ pivotRow, RowOp.factor ⟨0, h3⟩ 1] [] false
--         aesop
--       · let res := eliminateCol (factor M ⟨0, h3⟩ (M ⟨0, h3⟩ pivotCol)⁻¹) ⟨0, h3⟩ pivotCol
--             [RowOp.swap ⟨0, h3⟩ pivotRow, RowOp.factor ⟨0, h3⟩ (M ⟨0, h3⟩ pivotCol)⁻¹] false
--         have hlen : ([] : List (RowOp a R)).length ≥ res.2.length := by
--           have h' : (rrefAux res.1 1 1 res.2 false).2 = [] := by
--             rw [h1]
--           rw [← h']
--           apply row_reduction_adds_steps res.1 1 1 res.2 false
--         unfold res at hlen
--         have h_elim : (eliminateCol (factor M ⟨0, h3⟩ (M ⟨0, h3⟩ pivotCol)⁻¹) ⟨0, h3⟩ pivotCol
--             [RowOp.swap ⟨0, h3⟩ pivotRow,
--             RowOp.factor ⟨0, h3⟩ (M ⟨0, h3⟩ pivotCol)⁻¹] false).2.length
--             ≥ [RowOp.swap ⟨0, h3⟩ pivotRow, RowOp.factor ⟨0, h3⟩ 1].length := by
--           exact elim_col_adds_steps (factor M ⟨0, h3⟩ (M ⟨0, h3⟩ pivotCol)⁻¹) ⟨0, h3⟩ pivotCol
--             [RowOp.swap ⟨0, h3⟩ pivotRow, RowOp.factor ⟨0, h3⟩ (M ⟨0, h3⟩ pivotCol)⁻¹] [] false
--         aesop
--       · let res := eliminateCol (swapRow M ⟨0, h3⟩ pivotRow) ⟨0, h3⟩ pivotCol
--           [RowOp.swap ⟨0, h3⟩ pivotRow, RowOp.factor ⟨0, h3⟩ 1] false
--         have hlen : ([] : List (RowOp a R)).length ≥ res.2.length := by
--           have h' : (rrefAux res.1 1 1 res.2 false).2 = [] := by
--             rw [h1]
--           rw [← h']
--           apply row_reduction_adds_steps res.1 1 1 res.2 false
--         unfold res at hlen
--         have h_elim : (eliminateCol (swapRow M ⟨0, h3⟩ pivotRow) ⟨0, h3⟩ pivotCol
--           [RowOp.swap ⟨0, h3⟩ pivotRow, RowOp.factor ⟨0, h3⟩ 1] false).2.length
--             ≥ [RowOp.swap ⟨0, h3⟩ pivotRow, RowOp.factor ⟨0, h3⟩ 1].length := by
--           exact elim_col_adds_steps (swapRow M ⟨0, h3⟩ pivotRow) ⟨0, h3⟩ pivotCol
--             [RowOp.swap ⟨0, h3⟩ pivotRow, RowOp.factor ⟨0, h3⟩ 1] [] false
--         aesop
--       · let res := eliminateCol (factor (swapRow M ⟨0, h3⟩ pivotRow) ⟨0, h3⟩
--           (swapRow M ⟨0, h3⟩ pivotRow ⟨0, h3⟩ pivotCol)⁻¹) ⟨0, h3⟩ pivotCol
--           [RowOp.swap ⟨0, h3⟩ pivotRow,
--           RowOp.factor ⟨0, h3⟩ (swapRow M ⟨0, h3⟩ pivotRow ⟨0, h3⟩ pivotCol)⁻¹] false
--         have hlen : ([] : List (RowOp a R)).length ≥ res.2.length := by
--           have h' : (rrefAux res.1 1 1 res.2 false).2 = [] := by
--             rw [h1]
--           rw [← h']
--           apply row_reduction_adds_steps res.1 1 1 res.2 false
--         unfold res at hlen
--         have h_elim : (eliminateCol (factor (swapRow M ⟨0, h3⟩ pivotRow) ⟨0, h3⟩
--           (swapRow M ⟨0, h3⟩ pivotRow ⟨0, h3⟩ pivotCol)⁻¹) ⟨0, h3⟩ pivotCol
--           [RowOp.swap ⟨0, h3⟩ pivotRow,
--           RowOp.factor ⟨0, h3⟩ (swapRow M ⟨0, h3⟩ pivotRow ⟨0, h3⟩ pivotCol)⁻¹] false).2.length
--             ≥ [RowOp.swap ⟨0, h3⟩ pivotRow, RowOp.factor ⟨0, h3⟩ 1].length := by
--           exact elim_col_adds_steps (factor (swapRow M ⟨0, h3⟩ pivotRow) ⟨0, h3⟩
--             (swapRow M ⟨0, h3⟩ pivotRow ⟨0, h3⟩ pivotCol)⁻¹) ⟨0, h3⟩ pivotCol
--             [RowOp.swap ⟨0, h3⟩ pivotRow,
--             RowOp.factor ⟨0, h3⟩ (swapRow M ⟨0, h3⟩ pivotRow ⟨0, h3⟩ pivotCol)⁻¹] [] false
--         aesop
--     · rename_i a_ne
--       rw [← Fin.pos_iff_nonempty] at a_ne
--       contradiction
--   · rename_i op ops
--     aesop
--     -- Need to find decreasing measure, e.g. find a way to use `ops` instead of `op :: ops`
--     ·
--       have h1' : rowEchelonForm (M * Matrix.elementaryMatrixOfRowOp (RowOp.swap a_2 a_3)) = (U, ops) := by sorry
--       have := unfoldBuildPL ops M₁ M₂ (M * (Matrix.elementaryMatrixOfRowOp (RowOp.swap a_2 a_3))) ((Matrix.elementaryMatrixOfRowOp (RowOp.swap a_2 a_3)) * P) L U h1'
--       sorry
--       -- apply unfoldBuildPL (RowOp.swap a_2 a_3 :: ops) M₁ M₂ M P L U h1
--       -- exact h2
--     · apply unfoldBuildPL (RowOp.factor row scale :: ops) M₁ M₂ M P L U h1
--       exact h2
--     · apply unfoldBuildPL (RowOp.replace use toReplace scale :: ops) M₁ M₂ M P L U h1
--       exact h2

-- def unfoldBuildPL
>>>>>>> Stashed changes

theorem lu_matrix_eq_matrix (M : Matrix (Fin a) (Fin a) R)
    : (LUFactorization M).1 * (LUFactorization M).2.1 * (LUFactorization M).2.2 = M := by
  rw [LUFactorization]
  split
  · rename_i x₁ U steps heq₁
    split
    · rename_i x₂ P L heq₂
      simp

<<<<<<< Updated upstream
      -- Unfold buildPL call
      apply unfoldBuildPL steps 1 1 M P L U heq₁
      · exact heq₂
      · rename_i a_ne
        simp
        rw [Fin.pos_iff_nonempty]
        exact a_ne
=======
      rw [buildPL] at heq₂
      simp at heq₂
      apply unfoldBuildPL


      -- Old version
      -- -- Unfold buildPL call
      -- apply unfoldBuildPL steps 1 1 M P L U heq₁
      -- exact heq₂
>>>>>>> Stashed changes
