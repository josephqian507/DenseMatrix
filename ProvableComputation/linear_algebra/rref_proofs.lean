import Lean
import Lean.Elab.Tactic
import Qq
import Mathlib.Data.Matrix.Basic
import ProvableComputation.linear_algebra.Rref

open Matrix

variable {R : Type*}
variable {m n : Nat}
variable [Field R]
-- [Fintype m] [Fintype n] [DecidableEq m]

inductive step : Type where
  | skip : step         -- do nothing and move onto next column
  | op : step           -- factor then eliminate
  | swap : step         -- swap, factor, then eliminate
  | succ : step → step  -- go to next step

lemma mul_by_inv (A : Matrix (Fin m) (Fin m) R) (hA : Invertible A)
    (M : Matrix (Fin m) (Fin n) R) (x : Matrix (Fin n) (Fin 1) R) :
    (⅟A) * (M * x) = 0 ↔ M * x = 0 := by
  constructor
  · intro h
    -- apply A on the left to both sides of the equality (⅟A * M * x = 0)
    have h1 : A * (⅟A * (M * x)) = A * (0 : Matrix (Fin m) (Fin 1) R) := by rw [h]
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

def factor_proof {R : Type} [Field R] {a b : Nat} (M : Matrix (Fin a) (Fin b) R)
    (i : Fin a) (j : R) : M = factor M i j := by
  sorry

def eliminate_proof {R : Type} [Field R] {a b : Nat} (M : Matrix (Fin a) (Fin b) R)
    (pivotRow : Fin a) (pivotCol : Fin b) : M = eliminateCol M pivotRow pivotCol := by
  sorry
