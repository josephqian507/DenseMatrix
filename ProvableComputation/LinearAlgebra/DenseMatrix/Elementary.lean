/-
Copyright (c) 2026 Provable Computation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Provable Computation contributors
-/

import ProvableComputation.LinearAlgebra.DenseMatrix.Defs
import ProvableComputation.LinearAlgebra.GaussianElimination.Defs
import ProvableComputation.LinearAlgebra.GaussianElimination.Elementary

/-!
# DenseMatrix elementary operations

This module gives the dense representation the same elementary row-operation
surface as the function-backed `Matrix` implementation. The operations are
defined pointwise over dense storage, and the bridge lemmas below identify them
with the existing `Matrix` operations after `DenseMatrix.toMatrix`.
-/

namespace DenseMatrix

variable {m n : Nat}
variable {R : Type} [Field R] [DecidableEq R]

/-
The first block is row-major arithmetic rather than linear algebra.  All dense
elementary operations eventually update flat array positions, so the proofs need
a reusable way to recover the typed row and column from `i * n + j` and to know
when two flat offsets name the same matrix entry.
-/
private theorem rowMajorIndex_div (i : Fin m) (j : Fin n) :
    rowMajorIndex i j / n = i.val := by
  unfold rowMajorIndex
  rw [Nat.mul_comm i.val n]
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  rw [Nat.mul_add_div hn, Nat.div_eq_of_lt j.isLt, Nat.add_zero]

private theorem rowMajorIndex_mod (i : Fin m) (j : Fin n) :
    rowMajorIndex i j % n = j.val := by
  unfold rowMajorIndex
  rw [Nat.mul_comm i.val n]
  rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt j.isLt]

private theorem rowMajorIndex_inj {i1 i2 : Fin m} {j1 j2 : Fin n} :
    rowMajorIndex i1 j1 = rowMajorIndex i2 j2 ↔ i1 = i2 ∧ j1 = j2 := by
  constructor
  · intro h
    constructor
    · apply Fin.ext
      rw [← rowMajorIndex_div i1 j1, h, rowMajorIndex_div i2 j2]
    · apply Fin.ext
      rw [← rowMajorIndex_mod i1 j1, h, rowMajorIndex_mod i2 j2]
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem rowMajorIndex_lt_array {α : Type} {data : Array α}
    (hsize : data.size = m * n) (i : Fin m) (j : Fin n) :
    rowMajorIndex i j < data.size := by
  rw [hsize]
  exact rowMajorIndex_lt i j

/-
Row swaps are implemented by walking the column indices and swapping the two
flat slots for each column.  The companion lemmas record exactly what a read
sees when the requested column has already been processed or is still outside
the remaining work list.
-/
private def swapRowArray {α : Type} (data : Array α) (hsize : data.size = m * n)
    (row1 row2 : Fin m) : List (Fin n) → Vector α (m * n)
  | [] => Vector.mk data hsize
  | col :: cols =>
      swapRowArray
        (data.swap (rowMajorIndex row1 col) (rowMajorIndex row2 col)
          (rowMajorIndex_lt_array hsize row1 col)
          (rowMajorIndex_lt_array hsize row2 col))
        (by rw [Array.size_swap, hsize]) row1 row2 cols

private theorem get_swapRowArray_not_mem {α : Type}
    (data : Array α) (hsize : data.size = m * n) (row1 row2 : Fin m)
    (cols : List (Fin n)) (i : Fin m) (j : Fin n) (hmem : j ∉ cols) :
    (swapRowArray data hsize row1 row2 cols)[rowMajorIndex i j]'(rowMajorIndex_lt i j) =
      data[rowMajorIndex i j]'(rowMajorIndex_lt_array hsize i j) := by
  induction cols generalizing data hsize with
  | nil =>
      simp [swapRowArray, Vector.getElem_mk]
  | cons col cols ih =>
      simp only [List.mem_cons, not_or] at hmem
      have hcol_ne_j : col ≠ j := fun h => hmem.1 h.symm
      have h1 : rowMajorIndex i j ≠ rowMajorIndex row1 col := by
        intro hidx
        exact hcol_ne_j (rowMajorIndex_inj.mp hidx).2.symm
      have h2 : rowMajorIndex i j ≠ rowMajorIndex row2 col := by
        intro hidx
        exact hcol_ne_j (rowMajorIndex_inj.mp hidx).2.symm
      rw [swapRowArray]
      rw [ih (data := data.swap (rowMajorIndex row1 col) (rowMajorIndex row2 col)
          (rowMajorIndex_lt_array hsize row1 col)
          (rowMajorIndex_lt_array hsize row2 col))
        (hsize := by rw [Array.size_swap, hsize]) hmem.2]
      rw [Array.getElem_swap]
      simp [h1, h2]

private theorem get_swapRowArray_mem {α : Type}
    (data : Array α) (hsize : data.size = m * n) (row1 row2 : Fin m)
    (cols : List (Fin n)) (hnd : cols.Nodup)
    (i : Fin m) (j : Fin n) (hmem : j ∈ cols) :
    (swapRowArray data hsize row1 row2 cols)[rowMajorIndex i j]'(rowMajorIndex_lt i j) =
      if i = row1 then
        data[rowMajorIndex row2 j]'(rowMajorIndex_lt_array hsize row2 j)
      else if i = row2 then
        data[rowMajorIndex row1 j]'(rowMajorIndex_lt_array hsize row1 j)
      else
        data[rowMajorIndex i j]'(rowMajorIndex_lt_array hsize i j) := by
  induction cols generalizing data hsize with
  | nil =>
      cases hmem
  | cons col cols ih =>
      rw [swapRowArray]
      simp only [List.mem_cons] at hmem
      cases hmem with
      | inl hjeq =>
          subst col
          have hnot : j ∉ cols := (List.nodup_cons.mp hnd).1
          rw [get_swapRowArray_not_mem]
          · rw [Array.getElem_swap]
            by_cases hi1 : i = row1
            · subst i
              simp
            · by_cases hi2 : i = row2
              · subst i
                by_cases hrows : row2 = row1
                · subst row2
                  simp
                · have hne : rowMajorIndex row2 j ≠ rowMajorIndex row1 j := by
                    intro hidx
                    exact hrows (rowMajorIndex_inj.mp hidx).1
                  simp [hrows, hne]
              · have hne1 : rowMajorIndex i j ≠ rowMajorIndex row1 j := by
                  intro hidx
                  exact hi1 (rowMajorIndex_inj.mp hidx).1
                have hne2 : rowMajorIndex i j ≠ rowMajorIndex row2 j := by
                  intro hidx
                  exact hi2 (rowMajorIndex_inj.mp hidx).1
                simp [hi1, hi2, hne1, hne2]
          · exact hnot
      | inr hjmem =>
          have hnd_tail : cols.Nodup := List.Nodup.of_cons hnd
          rw [ih (data := data.swap (rowMajorIndex row1 col) (rowMajorIndex row2 col)
              (rowMajorIndex_lt_array hsize row1 col)
              (rowMajorIndex_lt_array hsize row2 col))
            (hsize := by rw [Array.size_swap, hsize]) hnd_tail hjmem]
          have hcol_ne_j : col ≠ j := by
            intro hc
            subst col
            exact (List.nodup_cons.mp hnd).1 hjmem
          have t21 : rowMajorIndex row2 j ≠ rowMajorIndex row1 col := by
            intro hidx
            exact hcol_ne_j (rowMajorIndex_inj.mp hidx).2.symm
          have t22 : rowMajorIndex row2 j ≠ rowMajorIndex row2 col := by
            intro hidx
            exact hcol_ne_j (rowMajorIndex_inj.mp hidx).2.symm
          have t11 : rowMajorIndex row1 j ≠ rowMajorIndex row1 col := by
            intro hidx
            exact hcol_ne_j (rowMajorIndex_inj.mp hidx).2.symm
          have t12 : rowMajorIndex row1 j ≠ rowMajorIndex row2 col := by
            intro hidx
            exact hcol_ne_j (rowMajorIndex_inj.mp hidx).2.symm
          have ti1 : rowMajorIndex i j ≠ rowMajorIndex row1 col := by
            intro hidx
            exact hcol_ne_j (rowMajorIndex_inj.mp hidx).2.symm
          have ti2 : rowMajorIndex i j ≠ rowMajorIndex row2 col := by
            intro hidx
            exact hcol_ne_j (rowMajorIndex_inj.mp hidx).2.symm
          simp [t21, t22, t11, t12, ti1, ti2]

private theorem get_swapRowArray_finRange {α : Type}
    (data : Array α) (hsize : data.size = m * n) (row1 row2 : Fin m)
    (i : Fin m) (j : Fin n) :
    (swapRowArray data hsize row1 row2 (List.finRange n))[
        rowMajorIndex i j]'(rowMajorIndex_lt i j) =
      if i = row1 then
        data[rowMajorIndex row2 j]'(rowMajorIndex_lt_array hsize row2 j)
      else if i = row2 then
        data[rowMajorIndex row1 j]'(rowMajorIndex_lt_array hsize row1 j)
      else
        data[rowMajorIndex i j]'(rowMajorIndex_lt_array hsize i j) :=
  get_swapRowArray_mem data hsize row1 row2 (List.finRange n)
    (List.nodup_finRange n) i j (List.mem_finRange j)

private theorem get_swapRowStorage {α : Type} (A : DenseMatrix m n α)
    (row1 row2 i : Fin m) (j : Fin n) :
    ({ data := swapRowArray A.data.toArray (by rw [Vector.size_toArray])
        row1 row2 (List.finRange n) } : DenseMatrix m n α).get i j =
      if i = row1 then A.get row2 j
      else if i = row2 then A.get row1 j
      else A.get i j := by
  simpa [DenseMatrix.get] using
    get_swapRowArray_finRange (data := A.data.toArray)
      (hsize := by rw [Vector.size_toArray]) row1 row2 i j

/-
Scaling and replacing a row both amount to setting every slot in one row.
Rather than proving those two public operations separately against raw arrays,
the `setRowArray` block proves a single storage update lemma parameterized by
the new row function.
-/
private def setRowArray {α : Type} (data : Array α) (hsize : data.size = m * n)
    (row : Fin m) (f : Fin n → α) : List (Fin n) → Vector α (m * n)
  | [] => Vector.mk data hsize
  | col :: cols =>
      setRowArray
        (data.set (rowMajorIndex row col) (f col)
          (rowMajorIndex_lt_array hsize row col))
        (by rw [Array.size_set, hsize]) row f cols

private theorem get_setRowArray_not_mem {α : Type}
    (data : Array α) (hsize : data.size = m * n) (row : Fin m)
    (f : Fin n → α) (cols : List (Fin n)) (i : Fin m) (j : Fin n)
    (hmem : j ∉ cols) :
    (setRowArray data hsize row f cols)[rowMajorIndex i j]'(rowMajorIndex_lt i j) =
      data[rowMajorIndex i j]'(rowMajorIndex_lt_array hsize i j) := by
  induction cols generalizing data hsize with
  | nil =>
      simp [setRowArray, Vector.getElem_mk]
  | cons col cols ih =>
      simp only [List.mem_cons, not_or] at hmem
      have hcol_ne_j : col ≠ j := fun h => hmem.1 h.symm
      have hne : rowMajorIndex row col ≠ rowMajorIndex i j := by
        intro hidx
        exact hcol_ne_j (rowMajorIndex_inj.mp hidx).2
      rw [setRowArray]
      rw [ih (data := data.set (rowMajorIndex row col) (f col)
          (rowMajorIndex_lt_array hsize row col))
        (hsize := by rw [Array.size_set, hsize]) hmem.2]
      rw [Array.getElem_set]
      simp [hne]

private theorem get_setRowArray_mem {α : Type}
    (data : Array α) (hsize : data.size = m * n) (row : Fin m)
    (f : Fin n → α) (cols : List (Fin n)) (hnd : cols.Nodup)
    (i : Fin m) (j : Fin n) (hmem : j ∈ cols) :
    (setRowArray data hsize row f cols)[rowMajorIndex i j]'(rowMajorIndex_lt i j) =
      if i = row then f j
      else data[rowMajorIndex i j]'(rowMajorIndex_lt_array hsize i j) := by
  induction cols generalizing data hsize with
  | nil =>
      cases hmem
  | cons col cols ih =>
      rw [setRowArray]
      simp only [List.mem_cons] at hmem
      cases hmem with
      | inl hjeq =>
          subst col
          have hnot : j ∉ cols := (List.nodup_cons.mp hnd).1
          rw [get_setRowArray_not_mem]
          · rw [Array.getElem_set]
            by_cases hi : i = row
            · subst i
              simp
            · have hne : rowMajorIndex row j ≠ rowMajorIndex i j := by
                intro hidx
                exact hi (rowMajorIndex_inj.mp hidx).1.symm
              simp [hi, hne]
          · exact hnot
      | inr hjmem =>
          have hnd_tail : cols.Nodup := List.Nodup.of_cons hnd
          rw [ih (data := data.set (rowMajorIndex row col) (f col)
              (rowMajorIndex_lt_array hsize row col))
            (hsize := by rw [Array.size_set, hsize]) hnd_tail hjmem]
          have hcol_ne_j : col ≠ j := by
            intro hc
            subst col
            exact (List.nodup_cons.mp hnd).1 hjmem
          have ti : rowMajorIndex row col ≠ rowMajorIndex i j := by
            intro hidx
            exact hcol_ne_j (rowMajorIndex_inj.mp hidx).2
          simp [Array.getElem_set, ti]

private theorem get_setRowArray_finRange {α : Type}
    (data : Array α) (hsize : data.size = m * n) (row : Fin m)
    (f : Fin n → α) (i : Fin m) (j : Fin n) :
    (setRowArray data hsize row f (List.finRange n))[
        rowMajorIndex i j]'(rowMajorIndex_lt i j) =
      if i = row then f j
      else data[rowMajorIndex i j]'(rowMajorIndex_lt_array hsize i j) :=
  get_setRowArray_mem data hsize row f (List.finRange n)
    (List.nodup_finRange n) i j (List.mem_finRange j)

private theorem get_setRowStorage {α : Type} (A : DenseMatrix m n α)
    (row i : Fin m) (f : Fin n → α) (j : Fin n) :
    ({ data := setRowArray A.data.toArray (by rw [Vector.size_toArray])
        row f (List.finRange n) } : DenseMatrix m n α).get i j =
      if i = row then f j else A.get i j := by
  simpa [DenseMatrix.get] using
    get_setRowArray_finRange (data := A.data.toArray)
      (hsize := by rw [Vector.size_toArray]) row f i j

/-
Column swaps are the row-major-unfriendly counterpart of row swaps: a single
column touches one slot in every row, so the loop walks `Fin m`.  The proof
shape mirrors the row-swap block to keep the DenseMatrix and Matrix bridge
lemmas symmetric.
-/
private def swapColArray {α : Type} (data : Array α) (hsize : data.size = m * n)
    (col1 col2 : Fin n) : List (Fin m) → Vector α (m * n)
  | [] => Vector.mk data hsize
  | row :: rows =>
      swapColArray
        (data.swap (rowMajorIndex row col1) (rowMajorIndex row col2)
          (rowMajorIndex_lt_array hsize row col1)
          (rowMajorIndex_lt_array hsize row col2))
        (by rw [Array.size_swap, hsize]) col1 col2 rows

private theorem get_swapColArray_not_mem {α : Type}
    (data : Array α) (hsize : data.size = m * n) (col1 col2 : Fin n)
    (rows : List (Fin m)) (i : Fin m) (j : Fin n) (hmem : i ∉ rows) :
    (swapColArray data hsize col1 col2 rows)[rowMajorIndex i j]'(rowMajorIndex_lt i j) =
      data[rowMajorIndex i j]'(rowMajorIndex_lt_array hsize i j) := by
  induction rows generalizing data hsize with
  | nil =>
      simp [swapColArray, Vector.getElem_mk]
  | cons row rows ih =>
      simp only [List.mem_cons, not_or] at hmem
      have hrow_ne_i : row ≠ i := fun h => hmem.1 h.symm
      have h1 : rowMajorIndex i j ≠ rowMajorIndex row col1 := by
        intro hidx
        exact hrow_ne_i (rowMajorIndex_inj.mp hidx).1.symm
      have h2 : rowMajorIndex i j ≠ rowMajorIndex row col2 := by
        intro hidx
        exact hrow_ne_i (rowMajorIndex_inj.mp hidx).1.symm
      rw [swapColArray]
      rw [ih (data := data.swap (rowMajorIndex row col1) (rowMajorIndex row col2)
          (rowMajorIndex_lt_array hsize row col1)
          (rowMajorIndex_lt_array hsize row col2))
        (hsize := by rw [Array.size_swap, hsize]) hmem.2]
      rw [Array.getElem_swap]
      simp [h1, h2]

private theorem get_swapColArray_mem {α : Type}
    (data : Array α) (hsize : data.size = m * n) (col1 col2 : Fin n)
    (rows : List (Fin m)) (hnd : rows.Nodup)
    (i : Fin m) (j : Fin n) (hmem : i ∈ rows) :
    (swapColArray data hsize col1 col2 rows)[rowMajorIndex i j]'(rowMajorIndex_lt i j) =
      if j = col1 then
        data[rowMajorIndex i col2]'(rowMajorIndex_lt_array hsize i col2)
      else if j = col2 then
        data[rowMajorIndex i col1]'(rowMajorIndex_lt_array hsize i col1)
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
            by_cases hj1 : j = col1
            · subst j
              simp
            · by_cases hj2 : j = col2
              · subst j
                by_cases hcols : col2 = col1
                · subst col2
                  simp
                · have hne : rowMajorIndex i col2 ≠ rowMajorIndex i col1 := by
                    intro hidx
                    exact hcols (rowMajorIndex_inj.mp hidx).2
                  simp [hcols, hne]
              · have hne1 : rowMajorIndex i j ≠ rowMajorIndex i col1 := by
                  intro hidx
                  exact hj1 (rowMajorIndex_inj.mp hidx).2
                have hne2 : rowMajorIndex i j ≠ rowMajorIndex i col2 := by
                  intro hidx
                  exact hj2 (rowMajorIndex_inj.mp hidx).2
                simp [hj1, hj2, hne1, hne2]
          · exact hnot
      | inr himem =>
          have hnd_tail : rows.Nodup := List.Nodup.of_cons hnd
          rw [ih (data := data.swap (rowMajorIndex row col1) (rowMajorIndex row col2)
              (rowMajorIndex_lt_array hsize row col1)
              (rowMajorIndex_lt_array hsize row col2))
            (hsize := by rw [Array.size_swap, hsize]) hnd_tail himem]
          have hrow_ne_i : row ≠ i := by
            intro hc
            subst row
            exact (List.nodup_cons.mp hnd).1 himem
          have t21 : rowMajorIndex i col2 ≠ rowMajorIndex row col1 := by
            intro hidx
            exact hrow_ne_i (rowMajorIndex_inj.mp hidx).1.symm
          have t22 : rowMajorIndex i col2 ≠ rowMajorIndex row col2 := by
            intro hidx
            exact hrow_ne_i (rowMajorIndex_inj.mp hidx).1.symm
          have t11 : rowMajorIndex i col1 ≠ rowMajorIndex row col1 := by
            intro hidx
            exact hrow_ne_i (rowMajorIndex_inj.mp hidx).1.symm
          have t12 : rowMajorIndex i col1 ≠ rowMajorIndex row col2 := by
            intro hidx
            exact hrow_ne_i (rowMajorIndex_inj.mp hidx).1.symm
          have ti1 : rowMajorIndex i j ≠ rowMajorIndex row col1 := by
            intro hidx
            exact hrow_ne_i (rowMajorIndex_inj.mp hidx).1.symm
          have ti2 : rowMajorIndex i j ≠ rowMajorIndex row col2 := by
            intro hidx
            exact hrow_ne_i (rowMajorIndex_inj.mp hidx).1.symm
          simp [t21, t22, t11, t12, ti1, ti2]

private theorem get_swapColArray_finRange {α : Type}
    (data : Array α) (hsize : data.size = m * n) (col1 col2 : Fin n)
    (i : Fin m) (j : Fin n) :
    (swapColArray data hsize col1 col2 (List.finRange m))[
        rowMajorIndex i j]'(rowMajorIndex_lt i j) =
      if j = col1 then
        data[rowMajorIndex i col2]'(rowMajorIndex_lt_array hsize i col2)
      else if j = col2 then
        data[rowMajorIndex i col1]'(rowMajorIndex_lt_array hsize i col1)
      else
        data[rowMajorIndex i j]'(rowMajorIndex_lt_array hsize i j) :=
  get_swapColArray_mem data hsize col1 col2 (List.finRange m)
    (List.nodup_finRange m) i j (List.mem_finRange i)

private theorem get_swapColStorage {α : Type} (A : DenseMatrix m n α)
    (col1 col2 : Fin n) (i : Fin m) (j : Fin n) :
    ({ data := swapColArray A.data.toArray (by rw [Vector.size_toArray])
        col1 col2 (List.finRange m) } : DenseMatrix m n α).get i j =
      if j = col1 then A.get i col2
      else if j = col2 then A.get i col1
      else A.get i j := by
  simpa [DenseMatrix.get] using
    get_swapColArray_finRange (data := A.data.toArray)
      (hsize := by rw [Vector.size_toArray]) col1 col2 i j

/-
Column scaling and replacement reuse the same idea as row updates, but with a
function of the row index.  Keeping this as a separate helper avoids hiding the
row-major access pattern behind transposition, which would be less useful for
runtime benchmarks.
-/
private def setColArray {α : Type} (data : Array α) (hsize : data.size = m * n)
    (col : Fin n) (f : Fin m → α) : List (Fin m) → Vector α (m * n)
  | [] => Vector.mk data hsize
  | row :: rows =>
      setColArray
        (data.set (rowMajorIndex row col) (f row)
          (rowMajorIndex_lt_array hsize row col))
        (by rw [Array.size_set, hsize]) col f rows

private theorem get_setColArray_not_mem {α : Type}
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
        exact hrow_ne_i (rowMajorIndex_inj.mp hidx).1
      rw [setColArray]
      rw [ih (data := data.set (rowMajorIndex row col) (f row)
          (rowMajorIndex_lt_array hsize row col))
        (hsize := by rw [Array.size_set, hsize]) hmem.2]
      rw [Array.getElem_set]
      simp [hne]

private theorem get_setColArray_mem {α : Type}
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
                exact hj (rowMajorIndex_inj.mp hidx).2.symm
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
            exact hrow_ne_i (rowMajorIndex_inj.mp hidx).1
          simp [Array.getElem_set, ti]

private theorem get_setColArray_finRange {α : Type}
    (data : Array α) (hsize : data.size = m * n) (col : Fin n)
    (f : Fin m → α) (i : Fin m) (j : Fin n) :
    (setColArray data hsize col f (List.finRange m))[
        rowMajorIndex i j]'(rowMajorIndex_lt i j) =
      if j = col then f i
      else data[rowMajorIndex i j]'(rowMajorIndex_lt_array hsize i j) :=
  get_setColArray_mem data hsize col f (List.finRange m)
    (List.nodup_finRange m) i j (List.mem_finRange i)

private theorem get_setColStorage {α : Type} (A : DenseMatrix m n α)
    (col : Fin n) (f : Fin m → α) (i : Fin m) (j : Fin n) :
    ({ data := setColArray A.data.toArray (by rw [Vector.size_toArray])
        col f (List.finRange m) } : DenseMatrix m n α).get i j =
      if j = col then f i else A.get i j := by
  simpa [DenseMatrix.get] using
    get_setColArray_finRange (data := A.data.toArray)
      (hsize := by rw [Vector.size_toArray]) col f i j

/-
The public DenseMatrix elementary operations preserve the names and edge-case
behavior of the existing Matrix operations.  The early exits for identity swaps,
unit scaling, and zero replacement keep the executable path cheap without
changing the bridge theorem that follows each operation.
-/
/-- Swap two rows of a dense matrix. -/
def swapRow (A : DenseMatrix m n R) (row1 row2 : Fin m) :
    DenseMatrix m n R :=
  if row1 = row2 then
    A
  else
    { data := swapRowArray A.data.toArray (by rw [Vector.size_toArray])
        row1 row2 (List.finRange n) }

/-- Scale one row of a dense matrix by a scalar. -/
def factor (A : DenseMatrix m n R) (i : Fin m) (c : R) :
    DenseMatrix m n R :=
  if c = 1 then
    A
  else
    { data := setRowArray A.data.toArray (by rw [Vector.size_toArray])
        i (fun j => c * A.get i j) (List.finRange n) }

/-- Compatibility alias for the older branch name. -/
abbrev scaleRow (A : DenseMatrix m n R) (i : Fin m) (c : R) :
    DenseMatrix m n R :=
  factor A i c

/-- Replace one dense row by itself plus a scalar multiple of another row. -/
def replace (A : DenseMatrix m n R) (use toReplace : Fin m) (k : R) :
    DenseMatrix m n R :=
  if k = 0 then
    A
  else if use = toReplace then
    factor A toReplace (k + 1)
  else
    { data := setRowArray A.data.toArray (by rw [Vector.size_toArray])
        toReplace (fun j => A.get toReplace j + k * A.get use j) (List.finRange n) }

/-- Compatibility alias for the older branch name. -/
abbrev replaceRow (A : DenseMatrix m n R) (use toReplace : Fin m) (k : R) :
    DenseMatrix m n R :=
  replace A use toReplace k

/-- Swap two columns of a dense matrix. -/
def swapCol (A : DenseMatrix m n R) (col1 col2 : Fin n) :
    DenseMatrix m n R :=
  if col1 = col2 then
    A
  else
    { data := swapColArray A.data.toArray (by rw [Vector.size_toArray])
        col1 col2 (List.finRange m) }

/-- Scale one column of a dense matrix by a scalar. -/
def factorCol (A : DenseMatrix m n R) (col : Fin n) (scale : R) :
    DenseMatrix m n R :=
  if scale = 1 then
    A
  else
    { data := setColArray A.data.toArray (by rw [Vector.size_toArray])
        col (fun i => scale * A.get i col) (List.finRange m) }

/--
Replace column `use` by itself plus `k` times column `toReplace`.

The argument order mirrors `ColumnElementary.replaceCol`, whose implementation is
used by the Matrix reference LU replay.
-/
def replaceCol (A : DenseMatrix m n R) (use toReplace : Fin n) (k : R) :
    DenseMatrix m n R :=
  if k = 0 then
    A
  else if use = toReplace then
    factorCol A use (k + 1)
  else
    { data := setColArray A.data.toArray (by rw [Vector.size_toArray])
        use (fun i => A.get i use + k * A.get i toReplace) (List.finRange m) }

/-
These bridge lemmas are the contract between the dense executable backend and
the existing Matrix proof development.  Once each dense operation is identified
extensionally after `toMatrix`, LU and determinant proofs can reuse the older
row-operation theorems instead of duplicating algebra over arrays.
-/
omit [Field R] [DecidableEq R] in
@[simp]
theorem toMatrix_swapRow (A : DenseMatrix m n R) (row1 row2 : Fin m) :
    (swapRow A row1 row2).toMatrix = _root_.swapRow A.toMatrix row1 row2 := by
  ext i j
  by_cases h : row1 = row2
  · subst row2
    by_cases hi : i = row1 <;> simp [swapRow, _root_.swapRow, DenseMatrix.toMatrix, hi]
  · rw [swapRow, if_neg h]
    simp [get_swapRowStorage, _root_.swapRow, DenseMatrix.toMatrix]

@[simp]
theorem toMatrix_factor (A : DenseMatrix m n R) (i : Fin m) (c : R) :
    (factor A i c).toMatrix = _root_.factor A.toMatrix i c := by
  ext i' j
  by_cases h : c = 1
  · subst c
    simp [factor, _root_.factor, DenseMatrix.toMatrix]
  · rw [factor, if_neg h]
    change
      ({ data := setRowArray A.data.toArray (by rw [Vector.size_toArray])
          i (fun j => c * A.get i j) (List.finRange n) } : DenseMatrix m n R).get i' j =
        _root_.factor A.toMatrix i c i' j
    rw [get_setRowStorage]
    by_cases hi : i' = i
    · subst i'
      simp [_root_.factor, DenseMatrix.toMatrix]
    · simp [_root_.factor, DenseMatrix.toMatrix, hi]

@[simp]
theorem toMatrix_replace
    (A : DenseMatrix m n R) (use toReplace : Fin m) (k : R) :
    (replace A use toReplace k).toMatrix = _root_.replace A.toMatrix use toReplace k := by
  by_cases hk : k = 0
  · subst k
    ext i j
    by_cases h : use = toReplace
    · subst use
      by_cases hi : i = toReplace
      · subst i
        simp [replace, _root_.replace, _root_.factor, DenseMatrix.toMatrix]
      · simp [replace, _root_.replace, _root_.factor, DenseMatrix.toMatrix]
    · by_cases hi : i = toReplace
      · subst i
        simp [replace, _root_.replace, DenseMatrix.toMatrix, h]
      · simp [replace, _root_.replace, DenseMatrix.toMatrix, h, hi]
  · by_cases h : use = toReplace
    · simp [replace, _root_.replace, hk, h]
    · rw [replace, _root_.replace, if_neg hk, if_neg h, if_neg h]
      ext i j
      simp [DenseMatrix.toMatrix, get_setRowStorage]

omit [Field R] [DecidableEq R] in
@[simp]
theorem toMatrix_swapCol (A : DenseMatrix m n R) (col1 col2 : Fin n) :
    (swapCol A col1 col2).toMatrix =
      (_root_.swapRow A.toMatrix.transpose col1 col2).transpose := by
  ext i j
  by_cases h : col1 = col2
  · subst col2
    by_cases hj : j = col1 <;> simp [swapCol, _root_.swapRow, DenseMatrix.toMatrix, hj]
  · rw [swapCol, if_neg h]
    simp [get_swapColStorage, _root_.swapRow, DenseMatrix.toMatrix]

@[simp]
theorem toMatrix_factorCol (A : DenseMatrix m n R) (col : Fin n) (scale : R) :
    (factorCol A col scale).toMatrix =
      (_root_.factor A.toMatrix.transpose col scale).transpose := by
  ext i j
  by_cases h : scale = 1
  · subst scale
    simp [factorCol, _root_.factor, DenseMatrix.toMatrix]
  · rw [factorCol, if_neg h]
    change
      ({ data := setColArray A.data.toArray (by rw [Vector.size_toArray])
          col (fun i => scale * A.get i col) (List.finRange m) } : DenseMatrix m n R).get i j =
        (_root_.factor A.toMatrix.transpose col scale).transpose i j
    rw [get_setColStorage]
    by_cases hj : j = col
    · subst j
      simp [_root_.factor, DenseMatrix.toMatrix]
    · simp [_root_.factor, DenseMatrix.toMatrix, hj]

@[simp]
theorem toMatrix_replaceCol
    (A : DenseMatrix m n R) (use toReplace : Fin n) (k : R) :
    (replaceCol A use toReplace k).toMatrix =
      (_root_.replace A.toMatrix.transpose toReplace use k).transpose := by
  by_cases hk : k = 0
  · subst k
    ext i j
    by_cases h : use = toReplace
    · subst toReplace
      by_cases hj : j = use
      · subst j
        simp [replaceCol, _root_.replace, _root_.factor, DenseMatrix.toMatrix]
      · simp [replaceCol, _root_.replace, _root_.factor, DenseMatrix.toMatrix]
    · have h' : toReplace ≠ use := fun hsym => h hsym.symm
      by_cases hj : j = use
      · subst j
        simp [replaceCol, _root_.replace, DenseMatrix.toMatrix, h']
      · simp [replaceCol, _root_.replace, DenseMatrix.toMatrix, h', hj]
  · by_cases h : use = toReplace
    · subst toReplace
      simp [replaceCol, _root_.replace, hk]
    · have h' : toReplace ≠ use := fun hsym => h hsym.symm
      rw [replaceCol, _root_.replace, if_neg hk, if_neg h, if_neg h']
      ext i j
      simp [DenseMatrix.toMatrix, get_setColStorage]

/-- Apply one logged row operation to a dense matrix. -/
def applyRowOp (A : DenseMatrix m n R) (op : RowOp m R) : DenseMatrix m n R :=
  match op with
  | .swap i j => swapRow A i j
  | .factor i c => factor A i c
  | .replace use toReplace k => replace A use toReplace k

@[simp]
theorem toMatrix_applyRowOp (A : DenseMatrix m n R) (op : RowOp m R) :
    (applyRowOp A op).toMatrix = Matrix.applyRowOp A.toMatrix op := by
  cases op <;> simp [applyRowOp, Matrix.applyRowOp]

/-
Pivot search is split into a row scan inside a column scan so Lean accepts a
simple structural termination measure.  It intentionally follows the Matrix
`checkPivot` order; row-reduction certificates depend on finding the same pivot
locations in the dense and function-backed paths.
-/
private def checkPivotScanRow
    (A : DenseMatrix m n R) (col : Nat) (hcol : col < n) (row : Nat) :
    Option (Fin m × Fin n) :=
  if hrow : row < m then
    if A.get ⟨row, hrow⟩ ⟨col, hcol⟩ ≠ 0 then
      some (⟨row, hrow⟩, ⟨col, hcol⟩)
    else
      checkPivotScanRow A col hcol (row + 1)
  else
    none
termination_by m - row
decreasing_by omega

private def checkPivotScanCol
    (A : DenseMatrix m n R) (startRow col : Nat) :
    Option (Fin m × Fin n) :=
  if hcol : col < n then
    match checkPivotScanRow A col hcol startRow with
    | some p => some p
    | none => checkPivotScanCol A startRow (col + 1)
  else
    none
termination_by n - col
decreasing_by omega

/-- Dense pivot search over the row-major backing storage. -/
def checkPivot (A : DenseMatrix m n R) (startRow startCol : Nat) :
    Option (Fin m × Fin n) :=
  checkPivotScanCol A startRow startCol

/-
The pivot-search bridge proves the dense scanner is not merely equivalent on
successful examples; it returns the exact same optional pivot at every recursive
state as the Matrix scanner.  That exactness is what lets dense REF/RREF reuse
the Matrix step-log correctness statements.
-/
private theorem checkPivotScanRow_eq_matrix
    (A : DenseMatrix m n R) (col : Nat) (hcol : col < n) (row : Nat) :
    checkPivotScanRow A col hcol row =
      _root_.checkPivot.scanCol.scanRow (M := A.toMatrix) col (hcol := hcol) row := by
  by_cases hrow : row < m
  · by_cases hval : A.get ⟨row, hrow⟩ ⟨col, hcol⟩ ≠ 0
    · have hvalMatrix :
          A.toMatrix ⟨row, hrow⟩ ⟨col, hcol⟩ ≠ 0 := by
        simpa [DenseMatrix.toMatrix] using hval
      rw [checkPivotScanRow, _root_.checkPivot.scanCol.scanRow]
      rw [dif_pos hrow, dif_pos hrow, if_pos hval, if_pos hvalMatrix]
    · have hvalMatrix :
          ¬ A.toMatrix ⟨row, hrow⟩ ⟨col, hcol⟩ ≠ 0 := by
        simpa [DenseMatrix.toMatrix] using hval
      rw [checkPivotScanRow, _root_.checkPivot.scanCol.scanRow]
      rw [dif_pos hrow, dif_pos hrow, if_neg hval, if_neg hvalMatrix]
      exact checkPivotScanRow_eq_matrix (A := A) (col := col) (hcol := hcol) (row := row + 1)
  · rw [checkPivotScanRow, _root_.checkPivot.scanCol.scanRow]
    rw [dif_neg hrow, dif_neg hrow]
termination_by m - row
decreasing_by omega

private theorem checkPivotScanCol_eq_matrix
    (A : DenseMatrix m n R) (startRow col : Nat) :
    checkPivotScanCol A startRow col =
      _root_.checkPivot.scanCol (M := A.toMatrix) startRow col := by
  by_cases hcol : col < n
  · cases hscan : checkPivotScanRow A col hcol startRow with
    | none =>
        have hscanMatrix :
            _root_.checkPivot.scanCol.scanRow (M := A.toMatrix) col (hcol := hcol) startRow =
              none := by
          simpa [checkPivotScanRow_eq_matrix (A := A) (col := col) (hcol := hcol)
            (row := startRow)] using hscan
        rw [checkPivotScanCol, _root_.checkPivot.scanCol]
        rw [dif_pos hcol, dif_pos hcol, hscan, hscanMatrix]
        exact checkPivotScanCol_eq_matrix (A := A) (startRow := startRow) (col := col + 1)
    | some p =>
        have hscanMatrix :
            _root_.checkPivot.scanCol.scanRow (M := A.toMatrix) col (hcol := hcol) startRow =
              some p := by
          simpa [checkPivotScanRow_eq_matrix (A := A) (col := col) (hcol := hcol)
            (row := startRow)] using hscan
        rw [checkPivotScanCol, _root_.checkPivot.scanCol]
        rw [dif_pos hcol, dif_pos hcol, hscan, hscanMatrix]
  · rw [checkPivotScanCol, _root_.checkPivot.scanCol]
    rw [dif_neg hcol, dif_neg hcol]
termination_by n - col
decreasing_by omega

@[simp]
theorem checkPivot_eq_matrix (A : DenseMatrix m n R) (startRow startCol : Nat) :
    checkPivot A startRow startCol = _root_.checkPivot A.toMatrix startRow startCol :=
  by
    simpa [checkPivot, _root_.checkPivot] using
      checkPivotScanCol_eq_matrix (A := A) (startRow := startRow) (col := startCol)

/-- Dense public result of a row-reduction routine. -/
structure RowReductionResult (m n : Nat) (R : Type) where
  matrix : DenseMatrix m n R
  steps : List (_root_.RowOp m R)

end DenseMatrix
