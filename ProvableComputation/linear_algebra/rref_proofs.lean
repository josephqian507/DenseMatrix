import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import ProvableComputation.linear_algebra.EchelonCommonProofs
import ProvableComputation.linear_algebra.Rref
import ProvableComputation.linear_algebra.RowEquivalent

open Matrix

variable {R : Type} [Field R]
variable {a b : Nat} [Nonempty (Fin a)] [Nonempty (Fin b)]

/- Row operation lemmas
-- Performing a row operation is equivalent to multiplying by the elementary matrix -/
lemma swap_matrix_eq_elem_mul_matrix (M : Matrix (Fin a) (Fin b) R) (r₁ r₂ : (Fin a))
    : swapRow M r₁ r₂ = (swapRow (1 : Matrix (Fin a) (Fin a) R) r₁ r₂) * M := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases h1 : i = r₁
  · -- Case 1: i = r₁
    simp [swapRow, h1, one_apply]
  · by_cases h2 : i = r₂
    · -- Case 2: i = r₂
      simp [swapRow, h2, one_apply]
    · -- Case 3: i ≠ r₁ and i ≠ r₂
      simp [swapRow, one_apply]

lemma factor_matrix_eq_elem_mul_matrix (M : Matrix (Fin a) (Fin b) R) (r : (Fin a)) (s : R)
    : factor M r s = (factor (1 : Matrix (Fin a) (Fin a) R) r s) * M := by
    ext i j
    rw [Matrix.mul_apply]
    by_cases hr : i = r
    · -- case 1 on the row of factorization (i=r)
      subst hr
      simp [factor, one_apply]
    · -- case 2 not on the row of factorization (i≠r)
      simp [factor, one_apply, hr]


lemma replace_matrix_eq_elem_mul_matrix (M : Matrix (Fin a) (Fin b) R) (use toReplace : (Fin a))
    (k : R)
    : replace M use toReplace k = (replace (1 : Matrix (Fin a) (Fin a) R) use toReplace k) * M := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases h1 : use = toReplace
  · -- Case 1: use = toReplace, so replace calls factor
    simp [replace, h1]

    -- NOTE: this is exactly the same as the second half of factor_matrix_eq_elem_mul_matrix
    by_cases hr : i = toReplace
    · -- case 1 on the row of factorization (i=r)
      subst hr
      simp [factor, one_apply]
    · -- case 2 not on the row of factorization (i≠r)
      simp [factor, one_apply, hr]
  · -- Case 2: use ≠ toReplace
    by_cases h2 : i = toReplace
    · -- Case 1: we are on the row to be replaced
      simp [replace, one_apply, h1, h2]
      ring_nf
      simp [Finset.sum_add_distrib]
    · -- Case 2: everything else
      simp [replace, one_apply, h1, h2]

/- Multiplying a matrix by an invertible matrix does not change its solution set -/
lemma mul_by_inv (A : Matrix (Fin a) (Fin a) R) (A_inv : Matrix (Fin a) (Fin a) R)
    (hA : A_inv * A = (1 : Matrix (Fin a) (Fin a) R))
    (M : Matrix (Fin a) (Fin b) R) (x : Matrix (Fin b) (Fin 1) R) :
    A * (M * x) = 0 ↔ M * x = 0 := by
  constructor
  · intro h
    -- apply A on the left to both sides of the equality (⅟A * M * x = 0)
    have h1 : A_inv * (A * (M * x)) = A_inv * (0 : Matrix (Fin a) (Fin 1) R) := by rw [h]
    -- reassociate so we can see (A * ⅟A) * (M * x)
    rw [←Matrix.mul_assoc] at h1
    -- use invertibility: A * ⅟A = 1
    rw [hA] at h1
    -- finish: 1 * (M * x) = M * x and A * 0 = 0
    simp at h1
    exact h1
  · intro h
    -- if M * x = 0, then (⅟A) * (M * x) = (⅟A) * 0 = 0
    simp [h]

variable [DecidableEq R]

/- Pivot is nonzero -/
def pivot_ne_zero (pivotRow : Fin a) (pivotCol : Fin b) (M : Matrix (Fin a) (Fin b) R)
    (r c : Nat) (h : checkPivot M r c = some (pivotRow, pivotCol))
    : M pivotRow pivotCol ≠ 0 := by
  rw [checkPivot, checkPivot.scanCol] at h
  split_ifs at h with h1
  · split at h
    · -- Case 1: found pivot in current column
      rename_i x p heq
      rw [checkPivot.scanCol.scanRow] at heq
      split_ifs at heq with h2 h3
      · -- Case 1a: found pivot in current row
        rw [h] at heq
        injection heq with heq
        cases heq
        exact h3
      · -- Case 1b: did not find pivot, scanning next row
        have h' : checkPivot M (r + 1) c = some (pivotRow, pivotCol) := by
          rw [checkPivot, checkPivot.scanCol]
          aesop
          -- split_ifs
          -- split
          -- · rename_i p' heq'
          --   rw [← heq', heq, h]
          -- · rename_i heq'
          --   rw [heq] at heq'
          --   contradiction
        -- Recursively call pivot_ne_zero over the structure of checkPivot
        exact pivot_ne_zero pivotRow pivotCol M (r + 1) c h'
    · -- Case 2: did not find pivot, scanning next column
      rename_i x heq
      have h' : checkPivot M r (c + 1) = some (pivotRow, pivotCol) := by
        aesop
        -- rw [checkPivot, checkPivot.scanCol]
        -- split_ifs with h2
        -- split
        -- · rename_i p heq'
        --   rw [checkPivot.scanCol] at h
        --   split_ifs at h
        --   split at h
        --   · rename_i p' heq''
        --     rw [← heq', heq'', h]
        --   · rename_i heq''
        --     rw [heq'] at heq''
        --     contradiction
        -- · rename_i heq'
        --   rw [checkPivot.scanCol] at h
        --   split_ifs at h
        --   split at h
        --   · rename_i heq''
        --     rw [heq'] at heq''
        --     contradiction
        --   · exact h
        -- · rw [checkPivot.scanCol] at h
        --   split_ifs at h
      -- Recursively call pivot_ne_zero over the structure of checkPivot
      exact pivot_ne_zero pivotRow pivotCol M r (c + 1) h'

/- Inverses of row operations -/
def swap_inv (M : Matrix (Fin a) (Fin b) R) (r₁ r₂ : Fin a)
    : swapRow (swapRow M r₁ r₂) r₁ r₂ = M := by
  ext i j
  simp only [swapRow, of_apply]
  split_ifs with h1 h2 h3
  · rw [h2, ← h1]
  · rw [← h1]
  · rw [← h3]
  · rfl

def factor_inv (M : Matrix (Fin a) (Fin b) R) (i : Fin a) (j : R) (hj : j ≠ 0)
    : factor (factor M i j) i j⁻¹ = M := by
  ext i j
  simp only [factor, of_apply]
  split_ifs with h1
  · simp [hj]
  · rfl


def replace_inv (M : Matrix (Fin a) (Fin b) R) (use toReplace : Fin a) (k : R) (h : use ≠ toReplace)
    : replace (replace M use toReplace k) use toReplace (-k) = M := by
  ext i j
  simp only [replace]
  split_ifs with h1
  · contradiction
  simp only [of_apply]
  split_ifs with h2
  · simp [h2]
  rfl

/- Applying each row operation does not change the matrix's solution set -/
def swap_proof {x : Matrix (Fin b) (Fin 1) R}
    (M : Matrix (Fin a) (Fin b) R) (r₁ r₂ : Fin a)
    : (swapRow M r₁ r₂) * x = 0 ↔ M * x = 0 := by
  -- Define A_inv and hA for mul_by_inv
  let A_inv : Matrix (Fin a) (Fin a) R := swapRow 1 r₁ r₂
  have hA : A_inv * (swapRow 1 r₁ r₂) = 1 := by
    rw [← swap_matrix_eq_elem_mul_matrix, swap_inv]
  rw [swap_matrix_eq_elem_mul_matrix, Matrix.mul_assoc]
  exact mul_by_inv _ A_inv hA M x

def factor_proof {x : Matrix (Fin b) (Fin 1) R} (M : Matrix (Fin a) (Fin b) R) (i : Fin a) (j : R)
    (hj : j ≠ 0)
    : (factor M i j) * x = 0 ↔ M * x = 0 := by
  let A_inv : Matrix (Fin a) (Fin a) R := factor 1 i j⁻¹
  have hA : A_inv * (factor 1 i j) = (1 : Matrix (Fin a) (Fin a) R) := by
    rw [← factor_matrix_eq_elem_mul_matrix, factor_inv]
    exact hj
  rw [factor_matrix_eq_elem_mul_matrix, Matrix.mul_assoc]
  exact mul_by_inv _ A_inv hA M x

def replace_proof {x : Matrix (Fin b) (Fin 1) R} (M : Matrix (Fin a) (Fin b) R)
    (use toReplace : Fin a) (k : R) (h : use ≠ toReplace)
    : (replace M use toReplace k) * x = 0 ↔ M * x = 0 := by
    let A_inv : Matrix (Fin a) (Fin a) R := replace 1 use toReplace (-k)
    have hA : A_inv * (replace 1 use toReplace k) = (1 : Matrix (Fin a) (Fin a) R) := by
      rw [← replace_matrix_eq_elem_mul_matrix, replace_inv]
      exact h
    rw [replace_matrix_eq_elem_mul_matrix, Matrix.mul_assoc]
    exact mul_by_inv _ A_inv hA M x

def eliminate_proof_helper (r : Fin a) (c : Fin b) (row : Nat) (M : Matrix (Fin a) (Fin b) R)
    (x : Matrix (Fin b) (Fin 1) R) (steps : List (RowOp a R)) (reduced : Bool)
    : (eliminateCol.go r c row M steps).1 * x = 0 ↔ M * x = 0 := by
  rw [eliminateCol.go]
  split
  · simp
    split_ifs with h1 h2
    · exact eliminate_proof_helper r c (row+1) M x steps reduced
    · exact eliminate_proof_helper r c (row+1) M x steps reduced
    · rw [eliminate_proof_helper, replace_proof]
      · push_neg at h1
        apply h1.symm
      · exact reduced
  · simp

def eliminate_proof {x : Matrix (Fin b) (Fin 1) R} (M : Matrix (Fin a) (Fin b) R)
    (r : Fin a) (c : Fin b) (steps : List (RowOp a R)) (reduced : Bool)
    : (eliminateCol M r c steps reduced).1 * x = 0 ↔ M * x = 0 := by
  rw [eliminateCol]
  split
  · exact eliminate_proof_helper r c 0 M x steps reduced
  · exact eliminate_proof_helper r c (↑r) M x steps reduced

/- Gaussian elimination does not change the matrix's solution set -/
def rref_proof_helper (M : Matrix (Fin a) (Fin b) R) (r c : Nat) (x : Matrix (Fin b) (Fin 1) R)
    (steps : List (RowOp a R)) (reduced : Bool)
    : (rrefAux M r c steps reduced).1 * x = 0 ↔ M * x = 0 := by
  rw [rrefAux]
  split_ifs with h1 h2
  · simp
    split
    · rfl
    rw [rref_proof_helper, eliminate_proof]
    split_ifs with h3 h4 h5
    · rfl
    · rw [factor_proof]
      rename_i pivotRow pivotCol heq
      have hr : pivotRow = ⟨r, h1⟩ := by
        ext
        exact h3
      rw [← hr]
      rw [ne_eq, inv_eq_iff_eq_inv, _root_.inv_zero]
      exact pivot_ne_zero pivotRow pivotCol M r c heq
    · rw [swap_proof]
    rw [factor_proof, swap_proof]
    rename_i pivotRow pivotCol heq
    rw [swapRow, of_apply]
    split_ifs with h6 h7
    · rw [ne_eq, inv_eq_iff_eq_inv, _root_.inv_zero]
      exact pivot_ne_zero pivotRow pivotCol M r c heq
    · rw [h7]
      rw [ne_eq, inv_eq_iff_eq_inv, _root_.inv_zero]
      exact pivot_ne_zero pivotRow pivotCol M r c heq
    · contradiction
  · rfl
  rfl

def ref_proof (M : Matrix (Fin a) (Fin b) R) (x : Matrix (Fin b) (Fin 1) R)
    : (rowEchelonForm M).1 * x = 0 ↔ M * x = 0 := by
  rw [rowEchelonForm]
  exact rref_proof_helper M 0 0 x List.nil false

def rref_proof (M : Matrix (Fin a) (Fin b) R) (x : Matrix (Fin b) (Fin 1) R)
    : (rowReducedEchelonForm M).1 * x = 0 ↔ M * x = 0 := by
  rw [rowReducedEchelonForm]
  exact rref_proof_helper M 0 0 x List.nil true

def elim_col_go_adds_steps_helper (pivotRow : Fin a) (pivotCol : Fin b) (r : Nat)
    (M : Matrix (Fin a) (Fin b) R) (steps : List (RowOp a R))
    : (eliminateCol.go pivotRow pivotCol r M steps).2.length ≥ steps.length := by
  rw [eliminateCol.go]
  split_ifs with h
  · simp
    split_ifs
    · rw [← ge_iff_le]
      exact elim_col_go_adds_steps_helper pivotRow pivotCol (r+1) M steps
    · rw [← ge_iff_le]
      exact elim_col_go_adds_steps_helper pivotRow pivotCol (r+1) M steps
    · rw [← ge_iff_le]
      trans (steps ++ [RowOp.replace pivotRow ⟨r, h⟩ (-M ⟨r, h⟩ pivotCol)]).length
      · exact elim_col_go_adds_steps_helper pivotRow pivotCol (r+1)
          (replace M pivotRow ⟨r, h⟩ (-M ⟨r, h⟩ pivotCol))
          (steps ++ [RowOp.replace pivotRow ⟨r, h⟩ (-M ⟨r, h⟩ pivotCol)])
      · aesop
  · simp

lemma elim_col_go_adds_steps (pivotRow : Fin a) (pivotCol : Fin b) (r : Nat)
    (M : Matrix (Fin a) (Fin b) R) (l1 l2 : List (RowOp a R))
    : (eliminateCol.go pivotRow pivotCol r M (l1 ++ l2)).2.length ≥ l1.length := by
  trans (l1 ++ l2).length
  · exact elim_col_go_adds_steps_helper pivotRow pivotCol r M (l1 ++ l2)
  · aesop

lemma elim_col_adds_steps (M : Matrix (Fin a) (Fin b) R) (pivotRow : Fin a) (pivotCol : Fin b)
    (l1 l2 : List (RowOp a R)) (reduced : Bool)
    : (eliminateCol M pivotRow pivotCol (l1 ++ l2) reduced).2.length ≥ l1.length := by
  rw [eliminateCol]
  split_ifs
  · exact elim_col_go_adds_steps pivotRow pivotCol 0 M l1 l2
  · exact elim_col_go_adds_steps pivotRow pivotCol (↑pivotRow) M l1 l2

theorem row_reduction_adds_steps (M : Matrix (Fin a) (Fin b) R) (r c : Nat)
    (steps : List (RowOp a R)) (reduced : Bool)
    : (rrefAux M r c steps reduced).2.length >= steps.length := by
  rw [rrefAux]
  aesop
  · let res := eliminateCol M pivotRow pivotCol
      (steps ++ [RowOp.swap pivotRow pivotRow, RowOp.factor pivotRow 1]) reduced
    rw [← ge_iff_le]
    trans res.2.length
    · exact row_reduction_adds_steps res.1 (↑pivotRow + 1) (c + 1) res.2 reduced
    · unfold res
      exact elim_col_adds_steps M pivotRow pivotCol steps
        [RowOp.swap pivotRow pivotRow, RowOp.factor pivotRow 1] reduced
  · let res := eliminateCol (factor M pivotRow (M pivotRow pivotCol)⁻¹) pivotRow pivotCol
      (steps ++ [RowOp.swap pivotRow pivotRow, RowOp.factor pivotRow (M pivotRow pivotCol)⁻¹])
      reduced
    rw [← ge_iff_le]
    trans res.2.length
    · exact row_reduction_adds_steps res.1 (↑pivotRow + 1) (c + 1) res.2 reduced
    · unfold res
      exact elim_col_adds_steps (factor M pivotRow (M pivotRow pivotCol)⁻¹) pivotRow pivotCol steps
        [RowOp.swap pivotRow pivotRow, RowOp.factor pivotRow (M pivotRow pivotCol)⁻¹] reduced
  · let res := eliminateCol (swapRow M ⟨r, h⟩ pivotRow) ⟨r, h⟩ pivotCol
      (steps ++ [RowOp.swap ⟨r, h⟩ pivotRow, RowOp.factor ⟨r, h⟩ 1]) reduced
    rw [← ge_iff_le]
    trans res.2.length
    · exact row_reduction_adds_steps res.1 (r + 1) (c + 1) res.2 reduced
    · unfold res
      exact elim_col_adds_steps (swapRow M ⟨r, h⟩ pivotRow) ⟨r, h⟩ pivotCol steps
        [RowOp.swap ⟨r, h⟩ pivotRow, RowOp.factor ⟨r, h⟩ 1] reduced
  · let res := eliminateCol
      (factor (swapRow M ⟨r, h⟩ pivotRow) ⟨r, h⟩ (swapRow M ⟨r, h⟩ pivotRow ⟨r, h⟩ pivotCol)⁻¹)
      ⟨r, h⟩ pivotCol (steps ++ [RowOp.swap ⟨r, h⟩ pivotRow,
      RowOp.factor ⟨r, h⟩ (swapRow M ⟨r, h⟩ pivotRow ⟨r, h⟩ pivotCol)⁻¹]) reduced
    rw [← ge_iff_le]
    trans res.2.length
    · exact row_reduction_adds_steps res.1 (r + 1) (c + 1) res.2 reduced
    · unfold res
      exact elim_col_adds_steps
        (factor (swapRow M ⟨r, h⟩ pivotRow) ⟨r, h⟩ (swapRow M ⟨r, h⟩ pivotRow ⟨r, h⟩ pivotCol)⁻¹)
        ⟨r, h⟩ pivotCol steps
        [RowOp.swap ⟨r, h⟩ pivotRow, RowOp.factor ⟨r, h⟩ (swapRow M ⟨r, h⟩ pivotRow ⟨r, h⟩ pivotCol)⁻¹]
        reduced

lemma empty_list_iff_no_change (M M' : Matrix (Fin a) (Fin b) R) (r c : Nat)
    (ops : List (RowOp a R)) (reduced : Bool)
    : rrefAux M r c ops reduced = (M', []) → M = M' := by
  unfold rrefAux
  split <;> simp
  · split_ifs with h1
    · split
      · simp
        sorry
      ·
        sorry
    ·
      sorry
  ·
    sorry

def steps_helper (M M' : Matrix (Fin a) (Fin b) R) (r c : Nat)
    (ops_head ops_tail ops_final : List (RowOp a R)) (reduced : Bool)
    (h_ops : ops_final = ops_head ++ ops_tail)
    : rrefAux M r c ops_head reduced = (M', ops_head ++ ops_tail) → ops_tail.foldl applyRowOp M = M' := by
  intro h
  rw [rrefAux] at h
  split_ifs at h with h1 h2
  · simp at h
    split at h
    · aesop
    · aesop
      ·
        sorry
      ·
        sorry
      ·
        sorry
      ·
        sorry
  ·
    sorry
  ·
    sorry

theorem steps (M M' : Matrix (Fin a) (Fin b) R) (ops : List (RowOp a R))
    : rowEchelonForm M = (M', ops) → ops.foldl applyRowOp M = M' := by
  intro h
  unfold rowEchelonForm at h
  induction ops with
  | nil =>
    rw [List.foldl_nil]
    have h_append : ([] : List (RowOp a R)) = [] ++ [] := by
      rw [List.append_nil]
    have hfold : [].foldl applyRowOp M = M' := by
      rw [steps_helper M M' 0 0 [] [] [] false h_append h]
    simp at hfold
    exact hfold
  | cons op ops' ih =>
    rw [List.foldl_cons]
    have h_append : op :: ops' = [] ++ op :: ops' := by
      rw [List.nil_append]
    have hfold : (op :: ops').foldl applyRowOp M = M' := by
      rw [steps_helper M M' 0 0 [] (op :: ops') (op :: ops') false h_append h]
    exact hfold

-- -- Folding over a list with one more element is applying the op to the previous result
-- omit [DecidableEq R] in
-- lemma foldl_applyRowOp_concat (M : Matrix (Fin a) (Fin b) R)
--     (ops : List (RowOp a R)) (op : RowOp a R)
--     : (ops.concat op).foldl applyRowOp M = applyRowOp (ops.foldl applyRowOp M) op := by
--   simp [List.foldl_append, applyRowOp]



-- def steps_helper (M M' : Matrix (Fin a) (Fin b) R) (r c : Nat) (ops : List (RowOp a R))
--     (reduced : Bool) : rrefAux M r c ops reduced = (M', ops) ↔ M' = ops.foldl applyRowOp M := by
--   rw [rrefAux]
--   split_ifs with h1 h2
--   · simp
--     split
--     · constructor
--       · intro h
--         rcases h
--         rw [List.foldl_nil]
--       · intro h

--         sorry
--     rw [steps_helper, eliminate_proof]
--     split_ifs with h3 h4 h5
--     · rfl
--     · rw [factor_proof]
--       rename_i pivotRow pivotCol heq
--       have hr : pivotRow = ⟨r, h1⟩ := by
--         ext
--         exact h3
--       rw [← hr]
--       rw [ne_eq, inv_eq_iff_eq_inv, _root_.inv_zero]
--       exact pivot_ne_zero pivotRow pivotCol M r c heq
--     · rw [swap_proof]
--     rw [factor_proof, swap_proof]
--     rename_i pivotRow pivotCol heq
--     rw [swapRow, of_apply]
--     split_ifs with h6 h7
--     · rw [ne_eq, inv_eq_iff_eq_inv, _root_.inv_zero]
--       exact pivot_ne_zero pivotRow pivotCol M r c heq
--     · rw [h7]
--       rw [ne_eq, inv_eq_iff_eq_inv, _root_.inv_zero]
--       exact pivot_ne_zero pivotRow pivotCol M r c heq
--     · contradiction
--   · rfl
--   rfl




-- lemma empty_list_iff_no_change (M M' : Matrix (Fin a) (Fin b) R) (r c : Nat) (ops : List (RowOp a R)) (reduced : Bool)
--     : rrefAux M r c ops reduced = (M', []) ↔ M = M' := by
--   unfold rrefAux
--   split <;> simp
--   · sorry
--   ·
--     sorry

-- theorem rrefAux_steps (m : Matrix (Fin a) (Fin b) R) (r c : Nat) (ops : List (RowOp a R))
--     (red : Bool) (M_init : Matrix (Fin a) (Fin b) R) (h_init : m = ops.foldl applyRowOp M_init)
--     : let (m_final, ops_final) := rrefAux m r c ops red
--       m_final = ops_final.foldl applyRowOp M_init := by
--   -- Proof by induction on the recursion of rrefAux
--   split
--   rename_i x m_final ops_final heq
--   induction ops_final with
--   | nil =>
--     rw [List.foldl_nil]
--     rw [empty_list_iff_no_change] at heq
--     sorry
--   | cons op ops' ih =>
--     sorry

-- /-- The final proof simply calls the generalized version -/
-- lemma steps (M M' : Matrix (Fin a) (Fin b) R) (ops : List (RowOp a R))
--     : rowEchelonForm M = (M', ops) ↔ M' = ops.foldl applyRowOp M := by
--   constructor
--   · intro h
--     unfold rowEchelonForm at h
--     induction ops with
--     | nil =>
--       rw [List.foldl_nil]
--       rw [empty_list_iff_no_change] at h
--       exact h.symm
--     | cons op ops' ih =>
--       rw [List.foldl_cons]
--       sorry
--   · intro h
--     sorry
