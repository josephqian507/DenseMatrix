import Mathlib.Data.Matrix.Basic
import ProvableComputation.linear_algebra.rref_proofs

namespace Matrix

variable {R : Type} [Field R] [DecidableEq R]

/- A row is zero if all of its entries are zero. -/
def RowIsZero {m n : Type*} (M : Matrix m n R) (i : m) : Prop :=
  ∀ j : n, M i j = 0

/- A pivot at column `p` of row `i`: the entry is nonzero and all entries to the left are zero. -/
def IsPivot {m n : Type*} [LinearOrder n] (M : Matrix m n R) (i : m) (p : n) : Prop :=
  M i p ≠ 0 ∧ ∀ j : n, j < p → M i j = 0

/- Row echelon form (REF) with respect to the given row/column orders. -/
structure IsEchelonForm {m n : Type*} [LinearOrder m] [LinearOrder n]
  (M : Matrix m n R) : Prop where
  row_zero_or_pivot :
    ∀ i : m, RowIsZero M i ∨ ∃ p : n, IsPivot M i p
  zero_rows_bottom :
    ∀ i j : m, i < j → RowIsZero M i → RowIsZero M j
  pivots_strictly_increasing :
    ∀ i j : m, ∀ p q : n, i < j → IsPivot M i p → IsPivot M j q → p < q

/- In REF, a pivot column is zero below the pivot (derivable from the minimal axioms). -/
omit [DecidableEq R] in
lemma IsEchelonForm.pivot_column_zero_below
    {m n : Type*} [LinearOrder m] [LinearOrder n]
    {M : Matrix m n R} (h : IsEchelonForm (M := M)) :
    ∀ i r : m, ∀ p : n, i < r → IsPivot M i p → M r p = 0 := by
  intro i r p hir hp
  cases h.row_zero_or_pivot r with
  | inl hzero =>
      exact hzero p
  | inr hex =>
      rcases hex with ⟨q, hq⟩
      have hlt : p < q := h.pivots_strictly_increasing i r p q hir hp hq
      exact hq.2 p hlt

section Reduced

variable [One R]

/- Reduced row echelon form (RREF): REF plus pivot normalization and zero above pivots. -/
structure IsReducedEchelonForm {m n : Type*} [LinearOrder m] [LinearOrder n]
  (M : Matrix m n R) : Prop where
  echelon : IsEchelonForm (M := M)
  pivot_is_one :
    ∀ i : m, ∀ p : n, IsPivot M i p → M i p = 1
  pivot_column_zero_above :
    ∀ i r : m, ∀ p : n, r < i → IsPivot M i p → M r p = 0

end Reduced

end Matrix
