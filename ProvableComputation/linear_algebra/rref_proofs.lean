import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import ProvableComputation.linear_algebra.EchelonCommonProofs
import ProvableComputation.linear_algebra.Rref
import ProvableComputation.linear_algebra.RowEquivalent

open Matrix

variable {R : Type} [Field R]
variable {a b : Nat}

omit [Field R] in
private lemma swapRow_self (M : Matrix (Fin a) (Fin b) R) (r : Fin a) :
    swapRow M r r = M := by
  ext i j
  by_cases h : i = r
  · simp [swapRow, h]
  · simp [swapRow, h]

private lemma factor_one (M : Matrix (Fin a) (Fin b) R) (r : Fin a) :
    factor M r 1 = M := by
  ext i j
  by_cases h : i = r
  · simp [factor, h]
  · simp [factor, h]

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

private theorem eliminateCol_go_log_correct
    (pivotRow : Fin a) (pivotCol : Fin b) (r : Nat)
    (M : Matrix (Fin a) (Fin b) R) (steps : List (RowOp a R)) :
    ∃ ops_tail : List (RowOp a R),
      eliminateCol.go pivotRow pivotCol r M steps =
        (ops_tail.foldl applyRowOp M, steps ++ ops_tail) := by
  have hrec :
      ∀ k (r : Nat) (M : Matrix (Fin a) (Fin b) R) (steps : List (RowOp a R)),
        a - r = k →
          ∃ ops_tail : List (RowOp a R),
            eliminateCol.go pivotRow pivotCol r M steps =
              (ops_tail.foldl applyRowOp M, steps ++ ops_tail) := by
    intro k
    induction k with
    | zero =>
        intro r M steps hk
        have hr : a ≤ r := Nat.le_of_sub_eq_zero hk
        refine ⟨[], ?_⟩
        simp [eliminateCol.go, Nat.not_lt_of_ge hr]
    | succ k ih =>
        intro r M steps hk
        have hr : r < a := by omega
        have hk' : a - (r + 1) = k := by omega
        let i : Fin a := ⟨r, hr⟩
        rw [eliminateCol.go, dif_pos hr]
        by_cases hEq : i = pivotRow
        · obtain ⟨ops_tail, htail⟩ := ih (r + 1) M steps hk'
          exact ⟨ops_tail, by simpa [i, hEq, dite_eq_ite] using htail⟩
        · by_cases hcoeff : M i pivotCol ≠ 0
          · let op : RowOp a R := .replace pivotRow i (-M i pivotCol)
            let M' := replace M pivotRow i (-M i pivotCol)
            let steps' := steps ++ [op]
            obtain ⟨ops_tail, htail⟩ := ih (r + 1) M' steps' hk'
            refine ⟨op :: ops_tail, ?_⟩
            simpa [i, hEq, hcoeff, op, M', steps', List.foldl_append, List.append_assoc,
              applyRowOp, dite_eq_ite] using htail
          · obtain ⟨ops_tail, htail⟩ := ih (r + 1) M steps hk'
            exact ⟨ops_tail, by simpa [i, hEq, hcoeff, dite_eq_ite] using htail⟩
  exact hrec (a - r) r M steps rfl

private theorem eliminateCol_log_correct
    (M : Matrix (Fin a) (Fin b) R) (pivotRow : Fin a) (pivotCol : Fin b)
    (steps : List (RowOp a R)) (reduced : Bool) :
    ∃ ops_tail : List (RowOp a R),
      eliminateCol M pivotRow pivotCol steps reduced =
        (ops_tail.foldl applyRowOp M, steps ++ ops_tail) := by
  rw [eliminateCol]
  by_cases hred : reduced
  · simpa [hred] using eliminateCol_go_log_correct pivotRow pivotCol 0 M steps
  · simpa [hred] using eliminateCol_go_log_correct pivotRow pivotCol pivotRow.1 M steps

private theorem rrefAux_log_correct
    (M : Matrix (Fin a) (Fin b) R) (r c : Nat)
    (steps : List (RowOp a R)) (reduced : Bool) :
    ∃ ops_tail : List (RowOp a R),
      rrefAux M r c steps reduced =
        (ops_tail.foldl applyRowOp M, steps ++ ops_tail) := by
  have hrec :
      ∀ k (M : Matrix (Fin a) (Fin b) R) (r c : Nat)
        (steps : List (RowOp a R)) (reduced : Bool),
        a - r = k →
          ∃ ops_tail : List (RowOp a R),
            rrefAux M r c steps reduced =
              (ops_tail.foldl applyRowOp M, steps ++ ops_tail) := by
    intro k
    induction k with
    | zero =>
        intro M r c steps reduced hk
        have hr : a ≤ r := Nat.le_of_sub_eq_zero hk
        refine ⟨[], ?_⟩
        simp [rrefAux, Nat.not_lt_of_ge hr]
    | succ k ih =>
        intro M r c steps reduced hk
        have hr : r < a := by omega
        have hk' : a - (r + 1) = k := by omega
        rw [rrefAux, dif_pos hr]
        by_cases hc : c < b
        · rw [if_pos hc]
          cases hcp : checkPivot M r c with
          | none =>
              refine ⟨[], ?_⟩
              simp
          | some p =>
              rcases p with ⟨pivotRow, pivotCol⟩
              let rowFin : Fin a := ⟨r, hr⟩
              let swapOp : RowOp a R := .swap rowFin pivotRow
              let steps1 : List (RowOp a R) := steps ++ [swapOp]
              let m1 : Matrix (Fin a) (Fin b) R :=
                if pivotRow.1 = r then M else swapRow M rowFin pivotRow
              have hm1 : m1 = applyRowOp M swapOp := by
                by_cases hswap : pivotRow.1 = r
                · have hpiv : pivotRow = rowFin := by
                    ext
                    simpa [rowFin] using hswap
                  subst hpiv
                  simp [m1, swapOp, applyRowOp, rowFin, swapRow_self]
                · simp [m1, swapOp, applyRowOp, hswap]
              let pivotVal : R := m1 rowFin pivotCol
              let factorOp : RowOp a R := .factor rowFin pivotVal⁻¹
              let steps2 : List (RowOp a R) := steps1 ++ [factorOp]
              let m2 : Matrix (Fin a) (Fin b) R :=
                if pivotVal = 1 then m1 else factor m1 rowFin pivotVal⁻¹
              have hm2 : m2 = applyRowOp m1 factorOp := by
                by_cases hpv : pivotVal = 1
                · simp [m2, factorOp, applyRowOp, hpv, factor_one]
                · simp [m2, factorOp, applyRowOp, hpv]
              obtain ⟨ops_elim, hElim⟩ :=
                eliminateCol_log_correct m2 rowFin pivotCol steps2 reduced
              obtain ⟨ops_rec, hRec⟩ :=
                ih (ops_elim.foldl applyRowOp m2) (r + 1) (c + 1) (steps2 ++ ops_elim) reduced hk'
              refine ⟨[swapOp, factorOp] ++ ops_elim ++ ops_rec, ?_⟩
              have hbranch :
                  (match eliminateCol m2 rowFin pivotCol steps2 reduced with
                    | (m3, steps3) => rrefAux m3 (r + 1) (c + 1) steps3 reduced) =
                    (ops_rec.foldl applyRowOp (ops_elim.foldl applyRowOp m2),
                      steps2 ++ ops_elim ++ ops_rec) := by
                simpa [hElim] using hRec
              have hfinal :
                  (ops_rec.foldl applyRowOp (ops_elim.foldl applyRowOp m2),
                    steps2 ++ ops_elim ++ ops_rec) =
                    (List.foldl applyRowOp M ([swapOp, factorOp] ++ ops_elim ++ ops_rec),
                      steps ++ ([swapOp, factorOp] ++ ops_elim ++ ops_rec)) := by
                apply Prod.ext
                · simp [steps1, steps2, List.foldl_append, List.append_assoc]
                  rw [hm2, hm1]
                · simp [steps1, steps2, List.append_assoc]
              simpa [hcp, rowFin, steps1, m1, pivotVal, steps2, m2, List.concat_eq_append] using
                hbranch.trans hfinal
        · refine ⟨[], ?_⟩
          simp [hc]
  exact hrec (a - r) M r c steps reduced rfl

lemma empty_list_iff_no_change (M M' : Matrix (Fin a) (Fin b) R) (r c : Nat)
    (ops : List (RowOp a R)) (reduced : Bool)
    : rrefAux M r c ops reduced = (M', []) → M = M' := by
  intro h
  obtain ⟨ops_tail, hlog⟩ := rrefAux_log_correct M r c ops reduced
  rw [hlog] at h
  injection h with hM hOps
  have hnil : ops_tail = [] := (List.eq_nil_of_append_eq_nil hOps).2
  simpa [hnil] using hM

theorem steps_helper (M M' : Matrix (Fin a) (Fin b) R) (r c : Nat)
    (ops_head ops_tail ops_final : List (RowOp a R)) (reduced : Bool)
    (h_ops : ops_final = ops_head ++ ops_tail)
    : rrefAux M r c ops_head reduced = (M', ops_head ++ ops_tail) →
        ops_tail.foldl applyRowOp M = M' := by
  intro h
  have h' : rrefAux M r c ops_head reduced = (M', ops_final) := by
    simpa [h_ops] using h
  obtain ⟨ops_tail', hlog⟩ := rrefAux_log_correct M r c ops_head reduced
  rw [hlog] at h'
  injection h' with hM hOps
  have hOps' : ops_head ++ ops_tail' = ops_head ++ ops_tail := by
    simpa [h_ops] using hOps
  have htail : ops_tail' = ops_tail := (List.append_right_inj ops_head).mp hOps'
  simpa [htail] using hM

theorem steps (M M' : Matrix (Fin a) (Fin b) R) (ops : List (RowOp a R))
    : rowEchelonForm M = (M', ops) → ops.foldl applyRowOp M = M' := by
  intro h
  have h_ops : ops = [] ++ ops := by simp
  have h' : rrefAux M 0 0 [] false = (M', [] ++ ops) := by
    simpa [rowEchelonForm]
  simpa using steps_helper M M' 0 0 [] ops ops false h_ops h'
