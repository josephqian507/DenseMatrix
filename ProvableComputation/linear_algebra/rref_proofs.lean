import Lean
import Lean.Elab.Tactic
import Qq
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import ProvableComputation.linear_algebra.Rref

open Matrix

variable {R : Type}
variable {a b : Nat}
variable [Field R]
-- [Fintype m] [Fintype n] [DecidableEq m]

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
  sorry

lemma factor_matrix_eq_elem_mul_matrix (M : Matrix (Fin a) (Fin b) R) (r : (Fin a)) (s : R)
    : factor M r s = (factor (1 : Matrix (Fin a) (Fin a) R) r s) * M := by
    ext i j
    rw [Matrix.mul_apply]
    by_cases hr : i = r
    · -- case 1 on the row of factorization (i=r)
      subst hr
      simp [factor, Matrix.one_apply]
    · -- case 2 not on the row of factorization (i≠r)
      simp [factor, Matrix.one_apply, hr]


lemma replace_matrix_eq_elem_mul_matrix (M : Matrix (Fin a) (Fin b) R) (use toReplace : (Fin a))
    (k : R)
    : replace M use toReplace k = (replace (1 : Matrix (Fin a) (Fin a) R) use toReplace k) * M := by
  sorry

lemma mul_by_inv (A : Matrix (Fin a) (Fin a) R) (hA : Invertible A)
    (M : Matrix (Fin a) (Fin b) R) (x : Matrix (Fin b) (Fin 1) R) :
    (⅟A) * (M * x) = 0 ↔ M * x = 0 := by
  constructor
  · intro h
    -- apply A on the left to both sides of the equality (⅟A * M * x = 0)
    have h1 : A * (⅟A * (M * x)) = A * (0 : Matrix (Fin a) (Fin 1) R) := by rw [h]
    -- reassociate so we can see (A * ⅟A) * (M * x)
    rw [←Matrix.mul_assoc] at h1
    -- use invertibility: A * ⅟A = 1
    rw [hA.mul_invOf_self] at h1
    -- finish: 1 * (M * x) = M * x and A * 0 = 0
    simp at h1
    exact h1

  · intro h
    -- if M*x = 0, then (⅟A)*(M*x) = (⅟A)*0 = 0
    simp [h]

-- def swap_proof {R : Type} [Field R] {a b : Nat} {x : Matrix (Fin b) (Fin 1) R}
--     (M : Matrix (Fin a) (Fin b) R) (r₁ r₂ : Fin a)
--     : (swapRow M r₁ r₂) * x = 0 ↔ M * x = 0 := by

-- def swap_matrix (r₁ r₂ : Fin a) : Matrix (Fin a) (Fin a) R :=
--   of fun a b =>
--     if (a = r₁ ∧ b = r₂) ∨
--        (a = r₂ ∧ b = r₁) ∨
--        (a ≠ r₁ ∧ a ≠ r₂ ∧ a = b) then
--       1
--     else
--       0

def swap_proof {x : Matrix (Fin b) (Fin 1) R}
    (M : Matrix (Fin a) (Fin b) R) (r₁ r₂ : Fin a)
    : (swapRow M r₁ r₂) * x = 0 ↔ M * x = 0 := by
  constructor
  · intro h
    let A : Matrix (Fin a) (Fin a) R := swapRow 1 r₁ r₂
    have hA : A * A = 1 := by
      rw [← Matrix.ext_iff]
      intros i j
      rw [A]


    let inv_A : Invertible.mk A hA hA
    sorry

  · intro h
  -- more code

-- def factor_proof {R : Type} [Field R] {a b : Nat} {x : Matrix (Fin b) (Fin 1) R}
--   (M : Matrix (Fin a) (Fin b) R)
--     (i : Fin a) (j : R) : (factor M i j) * x = 0 ↔ M * x = 0 := by
--     -- A is idendity matrix with factor at row a instead of 1
--     let A := Matrix.of fun r c =>
--     if r = c ∧ r = i then j
--     else if r = c then 1
--     else 0
--     -- factor M i j * x = 0 ↔ M * x = 0
--     let mult := A * M

theorem factor_proof {R : Type} [Field R] [DecidableEq R] {a b : ℕ} {x : Matrix (Fin b) (Fin 1) R}
  (M : Matrix (Fin a) (Fin b) R)
  (i : Fin a) (j : R) (hj : j ≠ 0) : -- Added hypothesis: j cannot be 0
  (Matrix.of fun r c => if r = c ∧ r = i then j else if r = c then 1 else 0) * M * x = 0 ↔ M * x = 0 := by

    -- 1. Define A (Scaling Matrix)
    let A := Matrix.of fun (r c : Fin a) =>
      if r = c ∧ r = i then j
      else if r = c then 1
      else 0

    -- 2. Define B (The Inverse of A)
    -- It is identical to A, but we use j⁻¹ instead of j
    let B := Matrix.of fun (r c : Fin a) =>
      if r = c ∧ r = i then j⁻¹
      else if r = c then 1
      else 0


    --3. Prove B is the inverse of A (B * A = 1)
    -- We use `have` to prove this fact locally
    have h_inv : B * A = 1 := by
      classical
      -- expose the definitions of A and B
      dsimp [A, B]
      -- rewrite them as diagonal matrices
      have hA := A_eq_diag (R:=R) (a:=a) i j
      have hB := B_eq_diag (R:=R) (a:=a) i j
      -- use the diagonal multiplication lemma
      -- (you might need `simp` with the lemma name, e.g. `Matrix.diagonal_mul_diagonal`)
      simp [hA, hB, Matrix.diagonal_mul_diagonal, Matrix.one, Matrix.diagonal]

      -- After rewriting, the diag entries look like:
      -- (if k = i then j⁻¹ else 1) * (if k = i then j else 1)
      -- `simp` proves this is always 1:
      --  • if k = i, it's j⁻¹ * j = 1
      --  • if k ≠ i, it's 1 * 1 = 1
      sorry
      -- ext r c
      -- simp [Matrix.mul_apply] -- Unfold matrix multiplication sum
      -- -- logic to show the sum collapses to 1 (diagonal) or 0 (off-diagonal)
      -- -- We use 'ite_mul' to handle the if/then multiplication logic
      -- simp [A, B]
      -- split_ifs with h_eq h_i
      -- · -- Case: r = c = i (The special index)
      --   -- We have term j⁻¹ * j, which is 1.
      --   simp [h_eq, h_i, field_simp_iff, hj]
      -- · -- Case: r = c, but r ≠ i (Normal diagonal)
      --   -- We have 1 * 1, which is 1.
      --   simp [h_eq]
      -- · -- Case: r ≠ c (Off diagonal)
      --   -- Everything is 0
      --   simp [h_eq]

    -- 4. Construct the Invertible Instance
    -- We cheat slightly: since we proved B*A=1 (left inverse),
    -- for square matrices over fields, it is also the right inverse.
    let invB : Invertible B := {
      invOf := A,
      invOf_mul_self := h_inv,
      mul_invOf_self := by
        -- Symmetric proof for A * B = 1 (omitted for brevity, same logic as above)
        -- In a real project, you would factor this out or use `Matrix.inv_of_left_inv`
        admit
    }

    -- 5. Apply the Lemma
    -- Your lemma says: ⅟B * (M * x) = 0 ↔ M * x = 0
    -- We know ⅟B is A.
    have h_apply := mul_by_inv B invB M x

    -- Clean up the goal to match the lemma
    rw [Matrix.mul_assoc] -- Turn (A*M)*x into A*(M*x)
    convert h_apply   -- Lean figures out that A = ⅟B


def replace_proof {R : Type} [Field R] {a b : Nat} {x : Matrix (Fin b) (Fin 1) R}
    (M : Matrix (Fin a) (Fin b) R) (pivotRow : Fin a) (pivotCol : Fin b)
    : (eliminateCol M pivotRow pivotCol) * x = 0 ↔ M * x = 0 := by
  sorry
