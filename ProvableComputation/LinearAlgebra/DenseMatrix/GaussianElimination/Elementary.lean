/-
Copyright (c) 2026 Provable Computation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Provable Computation contributors
-/

import ProvableComputation.LinearAlgebra.DenseMatrix.GaussianElimination.Defs

/-!
# Dense matrix elementary operations

This module provides identity and logged row operations together with elementary
column operations implemented directly on the row-major `Array` backing a
`DenseMatrix`.
-/

universe u

namespace DenseMatrix

variable {m n : Nat}

/-! ## Identity and row operations -/

private theorem toMatrix_injective {m n : Nat} {α : Type u} :
    Function.Injective (@DenseMatrix.toMatrix m n α) := by
  intro A B h
  calc
    A = ofMatrix (toMatrix A) := (ofMatrix_toMatrix A).symm
    _ = ofMatrix (toMatrix B) := congrArg ofMatrix h
    _ = B := ofMatrix_toMatrix B

/-- The dense identity matrix. -/
def identity {n : Nat} {α : Type u} [Zero α] [One α] [DecidableEq (Fin n)] :
    DenseMatrix n n α :=
  of fun i j => if i = j then 1 else 0

@[simp]
theorem get_identity {n : Nat} {α : Type u} [Zero α] [One α] [DecidableEq (Fin n)]
    (i j : Fin n) :
    (identity : DenseMatrix n n α).get i j = if i = j then 1 else 0 := by
  simp [identity]

@[simp]
theorem toMatrix_identity {n : Nat} {α : Type u} [Zero α] [One α] [DecidableEq (Fin n)] :
    toMatrix (identity : DenseMatrix n n α) = (1 : Matrix (Fin n) (Fin n) α) := by
  ext i j
  simp [identity, get_toMatrix, Matrix.one_apply]

@[simp]
theorem get_swapRow {m n : Nat} {α : Type u}
    (A : DenseMatrix m n α) (r₁ r₂ : Fin m) (i : Fin m) (j : Fin n) :
    (swapRow A r₁ r₂).get i j =
      if i = r₁ then A.get r₂ j else if i = r₂ then A.get r₁ j else A.get i j := by
  simp [swapRow]

@[simp]
theorem get_scaleRow {m n : Nat} {α : Type u} [Mul α]
    (A : DenseMatrix m n α) (r : Fin m) (c : α) (i : Fin m) (j : Fin n) :
    (scaleRow A r c).get i j = if i = r then c * A.get i j else A.get i j := by
  simp [scaleRow]

@[simp]
theorem get_replaceRow {m n : Nat} {α : Type u} [Semiring α]
    (A : DenseMatrix m n α) (src tgt : Fin m) (k : α) (i : Fin m) (j : Fin n) :
    (replaceRow A src tgt k).get i j =
      if i = tgt then A.get tgt j + k * A.get src j else A.get i j := by
  by_cases hst : src = tgt
  · subst tgt
    by_cases hi : i = src
    · subst i
      simp [replaceRow, add_mul, add_comm]
    · simp [replaceRow, hi]
  · simp [replaceRow, hst]

/-- Apply one shared row-operation certificate to a dense matrix. -/
def applyRowOp {m n : Nat} {α : Type u} [Semiring α]
    (A : DenseMatrix m n α) (op : RowOp m α) : DenseMatrix m n α :=
  match op with
  | .swap i j => swapRow A i j
  | .factor i c => scaleRow A i c
  | .replace src tgt k => replaceRow A src tgt k

/-- Elementary matrix corresponding to one shared row-operation certificate. -/
def elementaryMatrixOfRowOp {m : Nat} {α : Type u} [Semiring α] [NeZero m]
    (op : RowOp m α) : DenseMatrix m m α :=
  applyRowOp identity op

theorem elementaryMatrixOfRowOp_mul_eq_applyRowOp
    {m n : Nat} {α : Type u} [CommRing α] [Inhabited α] [NeZero m] [NeZero n]
    (op : RowOp m α) (A : DenseMatrix m n α) :
    elementaryMatrixOfRowOp op * A = applyRowOp A op := by
  apply toMatrix_injective
  change toMatrix (mul (elementaryMatrixOfRowOp op) A) = toMatrix (applyRowOp A op)
  rw [mul_toMatrix]
  cases op <;>
    simp [elementaryMatrixOfRowOp, applyRowOp, toMatrix_swap_eq_swap_toMatrix,
      toMatrix_scale_eq_scale_toMatrix, toMatrix_replace_eq_replace_toMatrix]

theorem swap_inv {m n : Nat} {α : Type u}
    (A : DenseMatrix m n α) (r₁ r₂ : Fin m) :
    swapRow (swapRow A r₁ r₂) r₁ r₂ = A := by
  apply toMatrix_injective
  ext i j
  simp only [get_toMatrix, get_swapRow]
  split_ifs with h1 h2 h3
  · rw [h2, ← h1]
  · rw [← h1]
  · rw [← h3]
  · rfl

theorem factor_inv {m n : Nat} {α : Type u} [Field α]
    (A : DenseMatrix m n α) (r : Fin m) (s : α) (hs : s ≠ 0) :
    scaleRow (scaleRow A r s) r s⁻¹ = A := by
  apply toMatrix_injective
  ext i j
  simp only [get_toMatrix, get_scaleRow]
  by_cases hi : i = r
  · simp [hi, hs]
  · simp [hi]

theorem replace_inv {m n : Nat} {α : Type u} [Ring α]
    (A : DenseMatrix m n α) (src tgt : Fin m) (k : α) (h : src ≠ tgt) :
    replaceRow (replaceRow A src tgt k) src tgt (-k) = A := by
  apply toMatrix_injective
  ext i j
  simp only [get_toMatrix, get_replaceRow]
  by_cases hi : i = tgt
  · simp [hi, h]
  · simp [hi]

/-! ## Array-backed column operations -/

private theorem rowMajorIndex_lt_array {α : Type u} {data : Array α}
    (hsize : data.size = m * n) (i : Fin m) (j : Fin n) :
    rowMajorIndex i j < data.size := by
  rw [hsize]
  exact rowMajorIndex_lt i j

/--
Thread an array through swaps of the two selected column slots in each listed
row.
-/
private def swapColArray {α : Type u} (data : Array α) (hsize : data.size = m * n)
    (c₁ c₂ : Fin n) : List (Fin m) → Vector α (m * n)
  | [] => Vector.mk data hsize
  | row :: rows =>
      swapColArray
        (data.swap (rowMajorIndex row c₁) (rowMajorIndex row c₂)
          (rowMajorIndex_lt_array hsize row c₁)
          (rowMajorIndex_lt_array hsize row c₂))
        (by rw [Array.size_swap, hsize]) c₁ c₂ rows

private theorem get_swapColArray_not_mem {α : Type u}
    (data : Array α) (hsize : data.size = m * n) (c₁ c₂ : Fin n)
    (rows : List (Fin m)) (i : Fin m) (j : Fin n) (hmem : i ∉ rows) :
    (swapColArray data hsize c₁ c₂ rows)[rowMajorIndex i j]'(rowMajorIndex_lt i j) =
      data[rowMajorIndex i j]'(rowMajorIndex_lt_array hsize i j) := by
  induction rows generalizing data hsize with
  | nil =>
      simp [swapColArray, Vector.getElem_mk]
  | cons row rows ih =>
      simp only [List.mem_cons, not_or] at hmem
      have hrow_ne_i : row ≠ i := fun h => hmem.1 h.symm
      have h₁ : rowMajorIndex i j ≠ rowMajorIndex row c₁ := by
        intro hidx
        exact hrow_ne_i (RowMajorIndex.eq_iff.mp hidx).1.symm
      have h₂ : rowMajorIndex i j ≠ rowMajorIndex row c₂ := by
        intro hidx
        exact hrow_ne_i (RowMajorIndex.eq_iff.mp hidx).1.symm
      rw [swapColArray]
      rw [ih (data := data.swap (rowMajorIndex row c₁) (rowMajorIndex row c₂)
          (rowMajorIndex_lt_array hsize row c₁)
          (rowMajorIndex_lt_array hsize row c₂))
        (hsize := by rw [Array.size_swap, hsize]) hmem.2]
      rw [Array.getElem_swap]
      simp [h₁, h₂]

private theorem get_swapColArray_mem {α : Type u}
    (data : Array α) (hsize : data.size = m * n) (c₁ c₂ : Fin n)
    (rows : List (Fin m)) (hnd : rows.Nodup)
    (i : Fin m) (j : Fin n) (hmem : i ∈ rows) :
    (swapColArray data hsize c₁ c₂ rows)[rowMajorIndex i j]'(rowMajorIndex_lt i j) =
      if j = c₁ then
        data[rowMajorIndex i c₂]'(rowMajorIndex_lt_array hsize i c₂)
      else if j = c₂ then
        data[rowMajorIndex i c₁]'(rowMajorIndex_lt_array hsize i c₁)
      else
        data[rowMajorIndex i j]'(rowMajorIndex_lt_array hsize i j) := by
  induction rows generalizing data hsize with
  | nil =>
      cases hmem
  | cons row rows ih =>
      rw [swapColArray]
      simp only [List.mem_cons] at hmem
      cases hmem with
      | inl hieq =>
          subst row
          have hnot : i ∉ rows := (List.nodup_cons.mp hnd).1
          rw [get_swapColArray_not_mem]
          · rw [Array.getElem_swap]
            by_cases hj₁ : j = c₁
            · subst j
              simp
            · by_cases hj₂ : j = c₂
              · subst j
                by_cases hcols : c₂ = c₁
                · subst c₂
                  simp
                · have hne : rowMajorIndex i c₂ ≠ rowMajorIndex i c₁ := by
                    intro hidx
                    exact hcols (RowMajorIndex.eq_iff.mp hidx).2
                  simp [hcols, hne]
              · have hne₁ : rowMajorIndex i j ≠ rowMajorIndex i c₁ := by
                  intro hidx
                  exact hj₁ (RowMajorIndex.eq_iff.mp hidx).2
                have hne₂ : rowMajorIndex i j ≠ rowMajorIndex i c₂ := by
                  intro hidx
                  exact hj₂ (RowMajorIndex.eq_iff.mp hidx).2
                simp [hj₁, hj₂, hne₁, hne₂]
          · exact hnot
      | inr himem =>
          have hnd_tail : rows.Nodup := List.Nodup.of_cons hnd
          rw [ih (data := data.swap (rowMajorIndex row c₁) (rowMajorIndex row c₂)
              (rowMajorIndex_lt_array hsize row c₁)
              (rowMajorIndex_lt_array hsize row c₂))
            (hsize := by rw [Array.size_swap, hsize]) hnd_tail himem]
          have hrow_ne_i : row ≠ i := by
            intro hc
            subst row
            exact (List.nodup_cons.mp hnd).1 himem
          have t₂₁ : rowMajorIndex i c₂ ≠ rowMajorIndex row c₁ := by
            intro hidx
            exact hrow_ne_i (RowMajorIndex.eq_iff.mp hidx).1.symm
          have t₂₂ : rowMajorIndex i c₂ ≠ rowMajorIndex row c₂ := by
            intro hidx
            exact hrow_ne_i (RowMajorIndex.eq_iff.mp hidx).1.symm
          have t₁₁ : rowMajorIndex i c₁ ≠ rowMajorIndex row c₁ := by
            intro hidx
            exact hrow_ne_i (RowMajorIndex.eq_iff.mp hidx).1.symm
          have t₁₂ : rowMajorIndex i c₁ ≠ rowMajorIndex row c₂ := by
            intro hidx
            exact hrow_ne_i (RowMajorIndex.eq_iff.mp hidx).1.symm
          have ti₁ : rowMajorIndex i j ≠ rowMajorIndex row c₁ := by
            intro hidx
            exact hrow_ne_i (RowMajorIndex.eq_iff.mp hidx).1.symm
          have ti₂ : rowMajorIndex i j ≠ rowMajorIndex row c₂ := by
            intro hidx
            exact hrow_ne_i (RowMajorIndex.eq_iff.mp hidx).1.symm
          simp [t₂₁, t₂₂, t₁₁, t₁₂, ti₁, ti₂]

private theorem get_swapColArray_finRange {α : Type u}
    (data : Array α) (hsize : data.size = m * n) (c₁ c₂ : Fin n)
    (i : Fin m) (j : Fin n) :
    (swapColArray data hsize c₁ c₂ (List.finRange m))[
        rowMajorIndex i j]'(rowMajorIndex_lt i j) =
      if j = c₁ then
        data[rowMajorIndex i c₂]'(rowMajorIndex_lt_array hsize i c₂)
      else if j = c₂ then
        data[rowMajorIndex i c₁]'(rowMajorIndex_lt_array hsize i c₁)
      else
        data[rowMajorIndex i j]'(rowMajorIndex_lt_array hsize i j) :=
  get_swapColArray_mem data hsize c₁ c₂ (List.finRange m)
    (List.nodup_finRange m) i j (List.mem_finRange i)

private theorem get_swapColStorage {α : Type u} (A : DenseMatrix m n α)
    (c₁ c₂ : Fin n) (i : Fin m) (j : Fin n) :
    ({ data := swapColArray A.data.toArray (by rw [Vector.size_toArray])
        c₁ c₂ (List.finRange m) } : DenseMatrix m n α).get i j =
      if j = c₁ then A.get i c₂
      else if j = c₂ then A.get i c₁
      else A.get i j := by
  simpa [DenseMatrix.get, Vector.get] using
    get_swapColArray_finRange (data := A.data.toArray)
      (hsize := by rw [Vector.size_toArray]) c₁ c₂ i j

/-- Thread an array through updates of one selected column in each listed row. -/
private def setColArray {α : Type u} (data : Array α) (hsize : data.size = m * n)
    (col : Fin n) (f : Fin m → α) : List (Fin m) → Vector α (m * n)
  | [] => Vector.mk data hsize
  | row :: rows =>
      setColArray
        (data.set (rowMajorIndex row col) (f row)
          (rowMajorIndex_lt_array hsize row col))
        (by rw [Array.size_set, hsize]) col f rows

private theorem get_setColArray_not_mem {α : Type u}
    (data : Array α) (hsize : data.size = m * n) (col : Fin n)
    (f : Fin m → α) (rows : List (Fin m)) (i : Fin m) (j : Fin n)
    (hmem : i ∉ rows) :
    (setColArray data hsize col f rows)[rowMajorIndex i j]'(rowMajorIndex_lt i j) =
      data[rowMajorIndex i j]'(rowMajorIndex_lt_array hsize i j) := by
  induction rows generalizing data hsize with
  | nil =>
      simp [setColArray, Vector.getElem_mk]
  | cons row rows ih =>
      simp only [List.mem_cons, not_or] at hmem
      have hrow_ne_i : row ≠ i := fun h => hmem.1 h.symm
      have hne : rowMajorIndex row col ≠ rowMajorIndex i j := by
        intro hidx
        exact hrow_ne_i (RowMajorIndex.eq_iff.mp hidx).1
      rw [setColArray]
      rw [ih (data := data.set (rowMajorIndex row col) (f row)
          (rowMajorIndex_lt_array hsize row col))
        (hsize := by rw [Array.size_set, hsize]) hmem.2]
      rw [Array.getElem_set]
      simp [hne]

private theorem get_setColArray_mem {α : Type u}
    (data : Array α) (hsize : data.size = m * n) (col : Fin n)
    (f : Fin m → α) (rows : List (Fin m)) (hnd : rows.Nodup)
    (i : Fin m) (j : Fin n) (hmem : i ∈ rows) :
    (setColArray data hsize col f rows)[rowMajorIndex i j]'(rowMajorIndex_lt i j) =
      if j = col then f i
      else data[rowMajorIndex i j]'(rowMajorIndex_lt_array hsize i j) := by
  induction rows generalizing data hsize with
  | nil =>
      cases hmem
  | cons row rows ih =>
      rw [setColArray]
      simp only [List.mem_cons] at hmem
      cases hmem with
      | inl hieq =>
          subst row
          have hnot : i ∉ rows := (List.nodup_cons.mp hnd).1
          rw [get_setColArray_not_mem]
          · rw [Array.getElem_set]
            by_cases hj : j = col
            · subst j
              simp
            · have hne : rowMajorIndex i col ≠ rowMajorIndex i j := by
                intro hidx
                exact hj (RowMajorIndex.eq_iff.mp hidx).2.symm
              simp [hj, hne]
          · exact hnot
      | inr himem =>
          have hnd_tail : rows.Nodup := List.Nodup.of_cons hnd
          rw [ih (data := data.set (rowMajorIndex row col) (f row)
              (rowMajorIndex_lt_array hsize row col))
            (hsize := by rw [Array.size_set, hsize]) hnd_tail himem]
          have hrow_ne_i : row ≠ i := by
            intro hc
            subst row
            exact (List.nodup_cons.mp hnd).1 himem
          have ti : rowMajorIndex row col ≠ rowMajorIndex i j := by
            intro hidx
            exact hrow_ne_i (RowMajorIndex.eq_iff.mp hidx).1
          simp [Array.getElem_set, ti]

private theorem get_setColArray_finRange {α : Type u}
    (data : Array α) (hsize : data.size = m * n) (col : Fin n)
    (f : Fin m → α) (i : Fin m) (j : Fin n) :
    (setColArray data hsize col f (List.finRange m))[
        rowMajorIndex i j]'(rowMajorIndex_lt i j) =
      if j = col then f i
      else data[rowMajorIndex i j]'(rowMajorIndex_lt_array hsize i j) :=
  get_setColArray_mem data hsize col f (List.finRange m)
    (List.nodup_finRange m) i j (List.mem_finRange i)

private theorem get_setColStorage {α : Type u} (A : DenseMatrix m n α)
    (col : Fin n) (f : Fin m → α) (i : Fin m) (j : Fin n) :
    ({ data := setColArray A.data.toArray (by rw [Vector.size_toArray])
        col f (List.finRange m) } : DenseMatrix m n α).get i j =
      if j = col then f i else A.get i j := by
  simpa [DenseMatrix.get, Vector.get] using
    get_setColArray_finRange (data := A.data.toArray)
      (hsize := by rw [Vector.size_toArray]) col f i j

/-- Swap two columns by swapping their two row-major slots in every row. -/
def swapCol {α : Type u} (A : DenseMatrix m n α) (c₁ c₂ : Fin n) :
    DenseMatrix m n α where
  data := swapColArray A.data.toArray (by rw [Vector.size_toArray])
    c₁ c₂ (List.finRange m)

/-- Scale one column by updating its row-major slot in every row. -/
def scaleCol {α : Type u} [Mul α] (A : DenseMatrix m n α) (c : Fin n) (s : α) :
    DenseMatrix m n α where
  data := setColArray A.data.toArray (by rw [Vector.size_toArray])
    c (fun i => s * A.get i c) (List.finRange m)

/--
Replace `tgt` by `tgt + k • src`. When `src = tgt`, this is implemented as
scaling that column by `k + 1`.
-/
def replaceCol {α : Type u} [Add α] [Mul α] [One α]
    (A : DenseMatrix m n α) (src tgt : Fin n) (k : α) : DenseMatrix m n α :=
  if src = tgt then
    scaleCol A tgt (k + 1)
  else
    { data := setColArray A.data.toArray (by rw [Vector.size_toArray])
        tgt (fun i => A.get i tgt + k * A.get i src) (List.finRange m) }

@[simp]
theorem get_swapCol {α : Type u} (A : DenseMatrix m n α) (c₁ c₂ : Fin n)
    (i : Fin m) (j : Fin n) :
    get (swapCol A c₁ c₂) i j =
      if j = c₁ then A.get i c₂
      else if j = c₂ then A.get i c₁
      else A.get i j :=
  get_swapColStorage A c₁ c₂ i j

@[simp]
theorem get_scaleCol {α : Type u} [Mul α] (A : DenseMatrix m n α) (c : Fin n) (s : α)
    (i : Fin m) (j : Fin n) :
    get (scaleCol A c s) i j =
      if j = c then s * A.get i c else A.get i j :=
  get_setColStorage A c (fun i => s * A.get i c) i j

@[simp]
theorem get_replaceCol {α : Type u} [Semiring α]
    (A : DenseMatrix m n α) (src tgt : Fin n) (k : α)
    (i : Fin m) (j : Fin n) :
    get (replaceCol A src tgt k) i j =
      if j = tgt then A.get i tgt + k * A.get i src else A.get i j := by
  by_cases hst : src = tgt
  · subst tgt
    by_cases hj : j = src
    · subst j
      simp [replaceCol, add_mul, add_comm]
    · simp [replaceCol, hj]
  · simp [replaceCol, hst, get_setColStorage]

/-- A dense column swap agrees with right multiplication by a swap matrix. -/
theorem toMatrix_swapCol_eq_mul_swap {α : Type u} [Semiring α]
    (A : DenseMatrix m n α) (c₁ c₂ : Fin n) :
    toMatrix (swapCol A c₁ c₂) = toMatrix A * Matrix.swap α c₁ c₂ := by
  ext i j
  change get (swapCol A c₁ c₂) i j = (toMatrix A * Matrix.swap α c₁ c₂) i j
  by_cases hj₁ : j = c₁
  · subst j
    simp [get_toMatrix]
  · by_cases hj₂ : j = c₂
    · subst j
      simp [hj₁, get_toMatrix]
    · rw [Matrix.mul_swap_of_ne hj₁ hj₂]
      simp [hj₁, hj₂, get_toMatrix]

/-- Dense column scaling agrees with right multiplication by a diagonal transvection. -/
theorem toMatrix_scaleCol_eq_mul_transvection {α : Type u} [CommRing α]
    (A : DenseMatrix m n α) (c : Fin n) (s : α) :
    toMatrix (scaleCol A c s) = toMatrix A * Matrix.transvection c c (s - 1) := by
  ext i j
  change
    get (scaleCol A c s) i j =
      (toMatrix A * Matrix.transvection c c (s - 1)) i j
  by_cases hj : j = c
  · subst j
    simp [get_toMatrix]
    ring
  · simp [hj, get_toMatrix]

/-- Dense column replacement agrees with right multiplication by a transvection. -/
theorem toMatrix_replaceCol_eq_mul_transvection {α : Type u} [CommRing α]
    (A : DenseMatrix m n α) (src tgt : Fin n) (k : α) :
    toMatrix (replaceCol A src tgt k) =
      toMatrix A * Matrix.transvection src tgt k := by
  ext i j
  change
    get (replaceCol A src tgt k) i j =
      (toMatrix A * Matrix.transvection src tgt k) i j
  by_cases hj : j = tgt
  · subst j
    simp [get_toMatrix]
  · simp [hj, get_toMatrix]

end DenseMatrix
