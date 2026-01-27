import Lean
import Lean.Elab.Tactic
import Qq
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import ProvableComputation.linear_algebra.Rref

open Matrix

variable {R : Type} [Field R] [DecidableEq R]
variable {a b : Nat}

/- Inductive type for lists of row operations -/
def is_swap (M N : Matrix (Fin a) (Fin b) R) : Prop := ∃ r₁ r₂ : (Fin a), swapRow M r₁ r₂ = N
def is_factor (M N : Matrix (Fin a) (Fin b) R) : Prop := ∃ (r : (Fin a)) (s : R), factor M r s = N
def is_replace (M N : Matrix (Fin a) (Fin b) R) : Prop :=
    ∃ (use toReplace : (Fin a)) (k : R), replace M use toReplace k = N
def is_row_equivalent (M N : Matrix (Fin a) (Fin b) R) : Prop :=
    is_swap M N ∨ is_factor M N ∨ is_replace M N

inductive row_equivalent_step : Matrix (Fin a) (Fin b) R → Matrix (Fin a) (Fin b) R → Type where
  | swap : ∀ (M : Matrix (Fin a) (Fin b) R) (r₁ r₂ : (Fin a)),
      row_equivalent_step M (swapRow M r₁ r₂)
  | factor : ∀ (M : Matrix (Fin a) (Fin b) R) (r : (Fin a)) (s : R),
      row_equivalent_step M (factor M r s)
  | replace : ∀ (M : Matrix (Fin a) (Fin b) R) (use toReplace : (Fin a)) (k : R),
      row_equivalent_step M (replace M use toReplace k)

inductive row_equivalence : Matrix (Fin a) (Fin b) R → Matrix (Fin a) (Fin b) R → Type where
  | nil : ∀ (M N : Matrix (Fin a) (Fin b) R) (h : row_equivalent_step M N), row_equivalence M N
  | cons : ∀ (M N L : Matrix (Fin a) (Fin b) R) (h₁ : row_equivalent_step M N)
      (h₂ : row_equivalent_step N L), row_equivalence M L

/- Row operation lemmas -/
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
  ext x y
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
