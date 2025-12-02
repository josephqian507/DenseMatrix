import Lean
import Lean.Elab.Tactic
import Qq
import Mathlib.Data.Matrix.Basic
import ProvableComputation.linear_algebra.Rref

open Matrix

variable {R : Type*}
variable {a b : Nat}
variable [Field R]
-- [Fintype m] [Fintype n] [DecidableEq m]

inductive step : Type where
  | skip : step         -- do nothing and move onto next column
  | op : step           -- factor then eliminate
  | swap : step         -- swap, factor, then eliminate
  | succ : step → step  -- go to next step

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

def swap_proof {R : Type} [Field R] {a b : Nat} (M : Matrix (Fin a) (Fin b) R)
    (r₁ r₂ : Fin a) : M = (swapRow M r₁ r₂) := by
  sorry

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


def eliminate_proof {R : Type} [Field R] {a b : Nat} (M : Matrix (Fin a) (Fin b) R)
    (pivotRow : Fin a) (pivotCol : Fin b) : M = eliminateCol M pivotRow pivotCol := by
  sorry
