/-
Copyright (c) 2026 Joseph Qian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Qian, Junye Ji, Dhruv Bhatia
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.Echelon.Basic
import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Echelon Predicates

This module defines row-echelon and reduced row-echelon predicates for matrices, together
with the basic structural lemma that pivot columns are zero below pivots in echelon form.
-/

universe v

variable {m n : Type*}
variable {R : Type v} {A : Matrix m n R}

namespace Matrix

/-! ## Echelon form -/

section EchelonOf

variable [CommRing R] [DecidableEq m] [Fintype m]

/-- `A` is a row-echelon-form representative of `B`. -/
structure IsRowEchelonOf [LT m] [LT n] (A B : Matrix m n R) : Prop where
  rowEquivalent : RowEquivalent A B
  isRowEchelon : IsRowEchelon A

/-- `A` is a reduced-row-echelon-form representative of `B`. -/
structure IsReducedRowEchelonOf [LT m] [LT n] (A B : Matrix m n R) : Prop where
  rowEquivalent : RowEquivalent A B
  isReducedRowEchelon : IsReducedRowEchelon A

/-- A reduced-echelon representative is also an echelon representative. -/
theorem IsReducedRowEchelonOf.isRowEchelon [LT m] [LT n] {A B : Matrix m n R}
    (h : IsReducedRowEchelonOf A B) : IsRowEchelonOf A B :=
  ⟨h.rowEquivalent, h.isReducedRowEchelon.isRowEchelon⟩

end EchelonOf

/-! ## Row equivalence -/

section RowEquivalent

variable [CommRing R] [DecidableEq m] [Fintype m]

/-- Row-equivalent matrices have the same homogeneous solution set. -/
theorem RowEquivalent.mul_eq_zero_iff [LT m] [Fintype n] {A B : Matrix m n R}
    (hAB : RowEquivalent A B)
    (x : n → R) :
    A *ᵥ x = 0 ↔ B *ᵥ x = 0 := by
  rcases hAB with ⟨U, rfl⟩
  constructor
  · intro h
    dsimp only
    simp only [HSMul.hSMul, SMul.smul]
    rw [←Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  · intro h
    have hmul := congrArg
      (fun Y : m → R ↦
        ((↑(U⁻¹) : Matrix m m R) *ᵥ Y)) h
    dsimp only at hmul
    rw [Matrix.mulVec_zero] at hmul
    simp only [HSMul.hSMul, SMul.smul] at hmul
    rw [Matrix.mulVec_mulVec] at hmul
    rw [← Matrix.mulVec_mulVec] at hmul
    rw [Matrix.mulVec_mulVec, ←Matrix.mul_assoc, ←Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul] at hmul
    exact hmul

/-- Row equivalent matrices have identical null spaces. -/
theorem RowEquivalent.ker_eq [Fintype n] {A B : Matrix m n R}
    (hAB : RowEquivalent A B) :
    LinearMap.ker (Matrix.mulVecLin A) = LinearMap.ker (Matrix.mulVecLin B) := by
  ext x
  rcases hAB with ⟨U, rfl⟩
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro h
    simp only [HSMul.hSMul, SMul.smul]
    rw [←Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  · intro h
    have hmul : ((U⁻¹ : (Matrix m m R)ˣ) : Matrix m m R) *ᵥ
        (((U : (Matrix m m R)ˣ) : Matrix m m R) *ᵥ (A *ᵥ x)) = 0 := by
      simp only [HSMul.hSMul, SMul.smul] at h
      nth_rewrite 2 [Matrix.mulVec_mulVec]
      rw [h, Matrix.mulVec_zero]
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at hmul
    exact hmul

/--
Matrices row-equivalent to a common source have the same homogeneous solution
set.
-/
theorem rowEquivalent_common_source_mul_eq_zero_iff
    [LT m] [Fintype n]
    {A B B' : Matrix m n R}
    (hAB : RowEquivalent A B)
    (hAB' : RowEquivalent A B')
    (x : n → R) :
    B *ᵥ x = 0 ↔ B' *ᵥ x = 0 := by
  have hBB' : RowEquivalent B B' :=
    RowEquivalent.trans (RowEquivalent.symm hAB) hAB'
  exact RowEquivalent.mul_eq_zero_iff hBB' x

end RowEquivalent

section RowEquivalentIffKernelEqual

variable [Field R] [DecidableEq m] [Fintype m]

theorem rowEquivalent_of_mul_eq_zero [Fintype n] {A B : Matrix m n R}
    (hAB : ∀ x : n → R, A *ᵥ x = 0 ↔ B *ᵥ x = 0) :
    RowEquivalent A B := by
  let _ := Classical.decEq n
  unfold RowEquivalent
  rw [MulAction.mem_orbit_iff]
  let f : (n → R) →ₗ[R] (m → R) := Matrix.toLin' A
  let g : (n → R) →ₗ[R] (m → R) := Matrix.toLin' B
  have hker : f.ker = g.ker := by
    ext x
    simp [f, g, Matrix.toLin'_apply, hAB x]
  let q : ((n → R) ⧸ f.ker) ≃ₗ[R] ((n → R) ⧸ g.ker) :=
    Submodule.quotEquivOfEq f.ker g.ker hker
  let eRange : f.range ≃ₗ[R] g.range :=
    f.quotKerEquivRange.symm.trans (q.trans g.quotKerEquivRange)
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq eRange
  have he_apply (x : n → R) : e (f x) = g x := by
    have hx := he ⟨f x, LinearMap.mem_range_self f x⟩
    change (eRange ⟨f x, LinearMap.mem_range_self f x⟩ : m → R) = e (f x) at hx
    simpa [eRange, q] using hx.symm
  let U : Matrix m m R := Matrix.toLin'.symm e.toLinearMap
  let Uinv : Matrix m m R := Matrix.toLin'.symm e.symm.toLinearMap
  have hU : Matrix.toLin' U = e.toLinearMap := by simp [U]
  have hUinv : Matrix.toLin' Uinv = e.symm.toLinearMap := by simp [Uinv]
  have hUUinv : U * Uinv = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_one, hU, hUinv]
    exact LinearMap.ext fun x => e.apply_symm_apply x
  have hUinvU : Uinv * U = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_one, hU, hUinv]
    exact LinearMap.ext fun x => e.symm_apply_apply x
  let u : GL m R := ⟨U, Uinv, hUUinv, hUinvU⟩
  have hBA : B = U * A := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, hU]
    apply LinearMap.ext
    intro x
    simpa [f, g] using (he_apply x).symm
  refine ⟨u, ?_⟩
  exact hBA.symm

/-- Two matrices over a field are row equivalent if and only if they have the same null space. -/
theorem rowEquivalent_iff_ker_eq [Fintype n]
    {A B : Matrix m n R} :
    RowEquivalent A B ↔ LinearMap.ker (mulVecLin A) = LinearMap.ker (mulVecLin B) := by
  constructor
  · exact RowEquivalent.ker_eq
  · intro hker
    apply rowEquivalent_of_mul_eq_zero
    intro x
    change x ∈ LinearMap.ker (mulVecLin A) ↔ x ∈ LinearMap.ker (mulVecLin B)
    rw [hker]

end RowEquivalentIffKernelEqual

/-! ## Leading entries -/

section LeadingEntry

variable [Zero R]

theorem row_eq_zero_or_exists_isLeadingEntry [LT n] [WellFoundedLT n] (i : m) :
        A i = 0 ∨ ∃ c, A.IsLeadingEntry i c := by
      by_cases hZero : A i = 0
      · exact Or.inl hZero
      · exact Or.inr (row_ne_zero_iff_exists_isLeadingEntry.mp hZero)

theorem IsRowEchelon.pivotCol_strictly_increasing [LT m] [LinearOrder n] {i j : m} {p q : n}
    (hA : A.IsRowEchelon) (hrow : i < j) (hi : A.IsLeadingEntry i p) (hj : A.IsLeadingEntry j q) :
    p < q := by
  by_contra h
  have hqp : q ≤ p := not_lt.mp h
  have h0 : ∀ j₁ < q, A i j₁ = 0 := fun j₁ hj₁ => hi.1 j₁ (lt_of_lt_of_le hj₁ hqp)
  exact hj.2 (hA hrow h0)

theorem not_isLeadingEntry_of_row_eq_zero [LT n] {i : m} {c : n}
    (h0 : A i = 0) : ¬ A.IsLeadingEntry i c := by
  intro hc
  exact hc.row_ne_zero h0

end LeadingEntry

end Matrix
