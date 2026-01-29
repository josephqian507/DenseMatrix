import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Field.Basic

variable {R : Type*} [Field R]
variable {a b : Nat}

def rowIsZero (M : Matrix (Fin a) (Fin b) R) (i : Fin a) : Prop :=
  ∀ j : Fin b, M i j = 0

def isPivot (M : Matrix (Fin a) (Fin b) R) (i : Fin a) (p : Fin b) : Prop :=
  M i p ≠ 0 ∧ ∀ j : Fin b, j < p → M i j = 0

structure isEchelonForm (M : Matrix (Fin a) (Fin b) R) : Prop where
  row_zero_or_pivot :
    ∀ i : Fin a, rowIsZero M i ∨ ∃ p : Fin b, isPivot M i p
  zero_rows_bottom :
    ∀ i j : Fin a, i < j → rowIsZero M i → rowIsZero M j
  pivots_strictly_increasing :
    ∀ i j : Fin a, ∀ p q : Fin b, i < j → isPivot M i p → isPivot M j q → p < q

lemma isEchelonForm.pivot_column_zero_below_of_increasing
    {M : Matrix (Fin a) (Fin b) R} (h : isEchelonForm (M := M)) :
    ∀ i r : Fin a, ∀ p : Fin b, i < r → isPivot M i p → M r p = 0 := by
  intro i r p hir hp
  cases h.row_zero_or_pivot r with
  | inl hzero =>
      exact hzero p
  | inr hex =>
      rcases hex with ⟨q, hq⟩
      have hlt : p < q := h.pivots_strictly_increasing i r p q hir hp hq
      exact hq.2 p hlt
