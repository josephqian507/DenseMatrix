import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import ProvableComputation.linear_algebra.IsInEchelonForm
import ProvableComputation.linear_algebra.Rref

namespace Matrix

variable {R : Type} [Field R]

/-- Row-equivalence via left multiplication by a unit square matrix. -/
def RowEquivalent {m n : Type*} [Fintype m] [DecidableEq m]
    (A B : Matrix m n R) : Prop :=
  ∃ U : (Matrix m m R)ˣ, B = (U : Matrix m m R) * A

lemma RowEquivalent.refl {m n : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m n R) : RowEquivalent A A := by
  refine ⟨1, ?_⟩
  simp

lemma RowEquivalent.symm {m n : Type*} [Fintype m] [DecidableEq m]
    {A B : Matrix m n R} (h : RowEquivalent A B) : RowEquivalent B A := by
  rcases h with ⟨U, rfl⟩
  refine ⟨U⁻¹, ?_⟩
  simp

lemma RowEquivalent.trans {m n : Type*} [Fintype m] [DecidableEq m]
    {A B C : Matrix m n R} (hAB : RowEquivalent A B) (hBC : RowEquivalent B C) :
    RowEquivalent A C := by
  rcases hAB with ⟨U, rfl⟩
  rcases hBC with ⟨V, rfl⟩
  refine ⟨V * U, ?_⟩
  simp [Matrix.mul_assoc]

instance rowEquivalentSetoid {m n : Type*} [Fintype m] [DecidableEq m] :
    Setoid (Matrix m n R) where
  r := RowEquivalent
  iseqv := ⟨RowEquivalent.refl, RowEquivalent.symm, RowEquivalent.trans⟩

/-- `B` is an echelon-form representative of `A`. -/
def IsEchelonFormOf {m n : Type*}
    [Fintype m] [DecidableEq m] [LinearOrder m] [LinearOrder n]
    (A B : Matrix m n R) : Prop :=
  RowEquivalent A B ∧ IsEchelonForm (M := B)

lemma IsEchelonFormOf.rowEquivalent {m n : Type*}
    [Fintype m] [DecidableEq m] [LinearOrder m] [LinearOrder n]
    {A B : Matrix m n R} (h : IsEchelonFormOf (A := A) B) :
    RowEquivalent A B :=
  h.1

lemma IsEchelonFormOf.echelon {m n : Type*}
    [Fintype m] [DecidableEq m] [LinearOrder m] [LinearOrder n]
    {A B : Matrix m n R} (h : IsEchelonFormOf (A := A) B) :
    IsEchelonForm (M := B) :=
  h.2

lemma isEchelonFormOf_mk {m n : Type*}
    [Fintype m] [DecidableEq m] [LinearOrder m] [LinearOrder n]
    {A B : Matrix m n R} (hRow : RowEquivalent A B) (hEch : IsEchelonForm (M := B)) :
    IsEchelonFormOf (A := A) B :=
  ⟨hRow, hEch⟩

section FinOperations

variable {a b : Nat}

private lemma swap_matrix_eq_elem_mul_matrix (M : Matrix (Fin a) (Fin b) R)
    (r₁ r₂ : Fin a) :
    swapRow M r₁ r₂ = (swapRow (1 : Matrix (Fin a) (Fin a) R) r₁ r₂) * M := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases h1 : i = r₁
  · simp [swapRow, h1, one_apply]
  · by_cases h2 : i = r₂
    · simp [swapRow, h2, one_apply]
    · simp [swapRow, one_apply]

private lemma factor_matrix_eq_elem_mul_matrix (M : Matrix (Fin a) (Fin b) R)
    (r : Fin a) (s : R) :
    factor M r s = (factor (1 : Matrix (Fin a) (Fin a) R) r s) * M := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hr : i = r
  · subst hr
    simp [factor, one_apply]
  · simp [factor, one_apply, hr]

private lemma replace_matrix_eq_elem_mul_matrix (M : Matrix (Fin a) (Fin b) R)
    (use toReplace : Fin a) (k : R) :
    replace M use toReplace k =
      (replace (1 : Matrix (Fin a) (Fin a) R) use toReplace k) * M := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases h1 : use = toReplace
  · simp [replace, h1]
    by_cases hr : i = toReplace
    · subst hr
      simp [factor, one_apply]
    · simp [factor, one_apply, hr]
  · by_cases h2 : i = toReplace
    · simp [replace, one_apply, h1, h2]
      ring_nf
      simp [Finset.sum_add_distrib]
    · simp [replace, one_apply, h1, h2]

omit [Field R] in
private lemma swap_inv (M : Matrix (Fin a) (Fin b) R) (r₁ r₂ : Fin a) :
    swapRow (swapRow M r₁ r₂) r₁ r₂ = M := by
  ext i j
  simp only [swapRow, of_apply]
  split_ifs with h1 h2 h3
  · rw [h2, ← h1]
  · rw [← h1]
  · rw [← h3]
  · rfl

private lemma factor_inv (M : Matrix (Fin a) (Fin b) R) (i : Fin a) (j : R) (hj : j ≠ 0) :
    factor (factor M i j) i j⁻¹ = M := by
  ext i j
  simp only [factor, of_apply]
  split_ifs with h1
  · simp [hj]
  · rfl

private lemma replace_inv
    (M : Matrix (Fin a) (Fin b) R) (use toReplace : Fin a) (k : R)
    (h : use ≠ toReplace) :
    replace (replace M use toReplace k) use toReplace (-k) = M := by
  ext i j
  simp only [replace]
  split_ifs with h1
  · contradiction
  simp only [of_apply]
  split_ifs with h2
  · simp [h2]
  · rfl

private lemma swap_elem_isUnit (r₁ r₂ : Fin a) :
    IsUnit (swapRow (1 : Matrix (Fin a) (Fin a) R) r₁ r₂) := by
  let E : Matrix (Fin a) (Fin a) R := swapRow (1 : Matrix (Fin a) (Fin a) R) r₁ r₂
  have hmul : E * E = (1 : Matrix (Fin a) (Fin a) R) := by
    calc
      E * E = swapRow E r₁ r₂ := by
        symm
        simpa [E] using (swap_matrix_eq_elem_mul_matrix (M := E) r₁ r₂)
      _ = (1 : Matrix (Fin a) (Fin a) R) := by
        simpa [E] using (swap_inv (M := (1 : Matrix (Fin a) (Fin a) R)) r₁ r₂)
  refine ⟨⟨E, E, hmul, hmul⟩, rfl⟩

private lemma factor_elem_isUnit (i : Fin a) (j : R) (hj : j ≠ 0) :
    IsUnit (factor (1 : Matrix (Fin a) (Fin a) R) i j) := by
  let E : Matrix (Fin a) (Fin a) R := factor (1 : Matrix (Fin a) (Fin a) R) i j
  let Einv : Matrix (Fin a) (Fin a) R := factor (1 : Matrix (Fin a) (Fin a) R) i j⁻¹
  have hleft : Einv * E = (1 : Matrix (Fin a) (Fin a) R) := by
    calc
      Einv * E = factor E i j⁻¹ := by
        symm
        simpa [E, Einv] using (factor_matrix_eq_elem_mul_matrix (M := E) (r := i) (s := j⁻¹))
      _ = (1 : Matrix (Fin a) (Fin a) R) := by
        simpa [E] using
          (factor_inv (M := (1 : Matrix (Fin a) (Fin a) R)) (i := i) (j := j) hj)
  have hrightAux : factor Einv i j = (1 : Matrix (Fin a) (Fin a) R) := by
    have hjinv : j⁻¹ ≠ 0 := inv_ne_zero hj
    simpa [Einv, hj] using
      (factor_inv (M := (1 : Matrix (Fin a) (Fin a) R)) (i := i) (j := j⁻¹) hjinv)
  have hright : E * Einv = (1 : Matrix (Fin a) (Fin a) R) := by
    calc
      E * Einv = factor Einv i j := by
        symm
        simpa [E, Einv] using (factor_matrix_eq_elem_mul_matrix (M := Einv) (r := i) (s := j))
      _ = (1 : Matrix (Fin a) (Fin a) R) := hrightAux
  refine ⟨⟨E, Einv, hright, hleft⟩, rfl⟩

private lemma replace_elem_isUnit (use toReplace : Fin a) (k : R) (huse : use ≠ toReplace) :
    IsUnit (replace (1 : Matrix (Fin a) (Fin a) R) use toReplace k) := by
  let E : Matrix (Fin a) (Fin a) R := replace (1 : Matrix (Fin a) (Fin a) R) use toReplace k
  let Einv : Matrix (Fin a) (Fin a) R := replace (1 : Matrix (Fin a) (Fin a) R) use toReplace (-k)
  have hleft : Einv * E = (1 : Matrix (Fin a) (Fin a) R) := by
    calc
      Einv * E = replace E use toReplace (-k) := by
        symm
        simpa [E, Einv] using
          (replace_matrix_eq_elem_mul_matrix (M := E) (use := use) (toReplace := toReplace)
            (k := -k))
      _ = (1 : Matrix (Fin a) (Fin a) R) := by
        simpa [E] using
          (replace_inv (M := (1 : Matrix (Fin a) (Fin a) R))
            (use := use) (toReplace := toReplace) (k := k) huse)
  have hrightAux : replace Einv use toReplace k = (1 : Matrix (Fin a) (Fin a) R) := by
    simpa [Einv] using
      (replace_inv (M := (1 : Matrix (Fin a) (Fin a) R))
        (use := use) (toReplace := toReplace) (k := -k) huse)
  have hright : E * Einv = (1 : Matrix (Fin a) (Fin a) R) := by
    calc
      E * Einv = replace Einv use toReplace k := by
        symm
        simpa [E, Einv] using
          (replace_matrix_eq_elem_mul_matrix (M := Einv) (use := use) (toReplace := toReplace)
            (k := k))
      _ = (1 : Matrix (Fin a) (Fin a) R) := hrightAux
  refine ⟨⟨E, Einv, hright, hleft⟩, rfl⟩

lemma rowEquivalent_swapRow
    (A : Matrix (Fin a) (Fin b) R) (r₁ r₂ : Fin a) :
    RowEquivalent A (swapRow A r₁ r₂) := by
  rcases swap_elem_isUnit (R := R) (a := a) r₁ r₂ with ⟨U, hU⟩
  refine ⟨U, ?_⟩
  calc
    swapRow A r₁ r₂
      = (swapRow (1 : Matrix (Fin a) (Fin a) R) r₁ r₂) * A := by
        simpa using (swap_matrix_eq_elem_mul_matrix (M := A) r₁ r₂)
    _ = (U : Matrix (Fin a) (Fin a) R) * A := by
        simp [hU]

lemma rowEquivalent_factor
    (A : Matrix (Fin a) (Fin b) R) (i : Fin a) (j : R) (hj : j ≠ 0) :
    RowEquivalent A (factor A i j) := by
  rcases factor_elem_isUnit (R := R) (a := a) i j hj with ⟨U, hU⟩
  refine ⟨U, ?_⟩
  calc
    factor A i j = (factor (1 : Matrix (Fin a) (Fin a) R) i j) * A := by
      simpa using (factor_matrix_eq_elem_mul_matrix (M := A) (r := i) (s := j))
    _ = (U : Matrix (Fin a) (Fin a) R) * A := by
      simp [hU]

lemma rowEquivalent_replace
    (A : Matrix (Fin a) (Fin b) R) (use toReplace : Fin a) (k : R)
    (huse : use ≠ toReplace) :
    RowEquivalent A (replace A use toReplace k) := by
  rcases replace_elem_isUnit (R := R) (a := a) use toReplace k huse with ⟨U, hU⟩
  refine ⟨U, ?_⟩
  calc
    replace A use toReplace k
      = (replace (1 : Matrix (Fin a) (Fin a) R) use toReplace k) * A := by
          simpa using
            (replace_matrix_eq_elem_mul_matrix (M := A) (use := use) (toReplace := toReplace)
              (k := k))
    _ = (U : Matrix (Fin a) (Fin a) R) * A := by
      simp [hU]

end FinOperations

section FirstPointExample

variable {R : Type} [Field R]

/-- A small source matrix for demonstrating `IsEchelonFormOf`. -/
def Afirst : Matrix (Fin 2) (Fin 2) R :=
  !![0, 0;
    1, 0]

/-- An echelon-form target matrix row-equivalent to `Afirst`. -/
def Bfirst : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0;
    0, 0]

lemma Bfirst_eq_swap : Bfirst (R := R) = swapRow (Afirst (R := R)) 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Bfirst, Afirst, swapRow, Matrix.of_apply]

private lemma Bfirst_row1_zero : RowIsZero (Bfirst (R := R)) 1 := by
  intro j
  fin_cases j <;> simp [Bfirst]

lemma Bfirst_isEchelon : IsEchelonForm (M := Bfirst (R := R)) := by
  refine IsEchelonForm.mk ?row_zero_or_pivot ?zero_rows_bottom ?pivots_strict
  · intro i
    fin_cases i
    · right
      refine ⟨(0 : Fin 2), ?_⟩
      refine ⟨?_, ?_⟩
      · simp [Bfirst]
      · intro j hj
        exact (False.elim ((Fin.not_lt_zero j) hj))
    · left
      exact Bfirst_row1_zero (R := R)
  · intro i j hij hzi
    fin_cases i <;> fin_cases j
    · exact (False.elim (lt_irrefl _ hij))
    · exfalso
      have h00 : (Bfirst (R := R)) 0 0 = 0 := hzi 0
      simp [Bfirst] at h00
    · exact (False.elim ((Nat.not_lt_zero _ (show (1 : Fin 2) < (0 : Fin 2) from hij))))
    · exact (False.elim (lt_irrefl _ hij))
  · intro i j p q hij hp hq
    fin_cases i <;> fin_cases j
    · exact (False.elim (lt_irrefl _ hij))
    · exfalso
      exact hq.1 ((Bfirst_row1_zero (R := R)) q)
    · exact (False.elim ((Nat.not_lt_zero _ (show (1 : Fin 2) < (0 : Fin 2) from hij))))
    · exact (False.elim (lt_irrefl _ hij))

/--
Concrete first-point example:
`Bfirst` is an echelon form of `Afirst` (row-equivalent + echelon predicate).
-/
theorem firstPointExample :
    IsEchelonFormOf (A := Afirst (R := R)) (Bfirst (R := R)) := by
  have hswap : RowEquivalent (Afirst (R := R)) (swapRow (Afirst (R := R)) 0 1) :=
    rowEquivalent_swapRow (A := Afirst (R := R)) (r₁ := 0) (r₂ := 1)
  have hRow : RowEquivalent (Afirst (R := R)) (Bfirst (R := R)) := by
    simpa [Bfirst_eq_swap (R := R)] using hswap
  exact isEchelonFormOf_mk (hRow := hRow) (hEch := Bfirst_isEchelon (R := R))

end FirstPointExample

end Matrix
