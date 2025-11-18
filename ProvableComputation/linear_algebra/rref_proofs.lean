import Lean
import Lean.Elab.Tactic
import Qq
import Mathlib.Data.Matrix.Basic

open Matrix

def mul_by_inv {R : Type} {m n : Nat} [Semiring R] (x : Matrix (Fin n) (Fin 1) R)
    (M : Matrix (Fin m) (Fin n) R) (A : Matrix (Fin m) (Fin m) R) [Invertible A]
    : ⅟A * M * x = 0 ↔ M * x = 0 := by
  sorry
