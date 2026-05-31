/-
Copyright (c) 2026 Provable Computation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Provable Computation contributors
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Matrix.Basic

/-!
# Dense matrix basics

This file contains only the minimal Vector-backed representation for dense
matrices and the bridge to mathlib's function-backed `Matrix` type.

The dimensions are tracked by the storage type itself: a value of
`DenseMatrix m n α` stores exactly `m * n` entries in one `Vector α (m * n)`.
Entries are flattened in row-major order, so row `i`, column `j` lives at offset
`i * n + j`.
-/

-- The universe parameter keeps `DenseMatrix` polymorphic over element types.
universe u

/--
Row-major matrix with dimensions tracked in the type.

The raw storage is the `data` field. Its `Vector` length is the representation
invariant, so callers index by `Fin m` and `Fin n` rather than by unchecked
natural-number offsets.
-/
structure DenseMatrix (m n : Nat) (α : Type u) where
  data : Vector α (m * n)
deriving Repr

-- All operations and helper lemmas for dense matrices live under this namespace.
namespace DenseMatrix

/--
Row-major offset for an entry of an `m` by `n` dense matrix.

For row `i` and column `j`, all entries in earlier rows contribute `i.val * n`
slots, and `j.val` selects the slot inside the current row. The companion
theorem `rowMajorIndex_lt` proves that this offset is inside the storage
interval `[0, m * n)`.
-/
def rowMajorIndex {m n : Nat} (i : Fin m) (j : Fin n) : Nat :=
  i.val * n + j.val

/--
The row-major offset is always a valid index into the flat storage vector.

The proof bounds `j` by the width `n`, rewrites the next row boundary as
`(i.val + 1) * n`, then uses `i.isLt` to stay below `m * n`.
-/
theorem rowMajorIndex_lt {m n : Nat} (i : Fin m) (j : Fin n) :
    rowMajorIndex i j < m * n := by
  unfold rowMajorIndex
  calc
    i.val * n + j.val < i.val * n + n := Nat.add_lt_add_left j.isLt (i.val * n)
    _ = (i.val + 1) * n := by rw [Nat.succ_mul]
    _ ≤ m * n := Nat.mul_le_mul_right n (Nat.succ_le_iff.mpr i.isLt)

/--
Unchecked row-major fast-path read.

The row and column are natural numbers, not typed `Fin` indices. This function
does not prove that `i < m`, `j < n`, or `i * n + j < m * n`; callers are
responsible for those bounds when they want matrix semantics. Prefer `get` when
typed indices are available.
-/
@[inline]
def get! {m n : Nat} {α : Type u} [Inhabited α] (M : DenseMatrix m n α) (i j : Nat) : α :=
  M.data[i * n + j]!

/--
Unchecked row-major fast-path update.

The row and column are natural numbers, not typed `Fin` indices. This function
computes the row-major offset `i * n + j` without carrying a bounds proof, so
callers are responsible for ensuring the offset is inside the backing vector.
Prefer `set` when typed indices are available.
-/
@[inline]
def set! {m n : Nat} {α : Type u} [Inhabited α] (M : DenseMatrix m n α) (i j : Nat) (val : α)
    : DenseMatrix m n α where
  data := M.data.set! (i * n + j) val

/--
Read an entry using checked row-major indexing.

The value-level index is computed by `rowMajorIndex`; the paired proof
`rowMajorIndex_lt` turns that offset into a `Fin (m * n)`. Thus `get` has no
unchecked fallback and no default value.
-/
@[inline]
def get {m n : Nat} {α : Type u} (A : DenseMatrix m n α) (i : Fin m) (j : Fin n) : α :=
  A.data.get ⟨rowMajorIndex i j, rowMajorIndex_lt i j⟩

/--
Return a matrix with one entry updated.

The update uses the same checked row-major offset as `get`; the `Vector` result
keeps the same length by construction.
-/
@[inline]
def set {m n : Nat} {α : Type u} (A : DenseMatrix m n α) (i : Fin m) (j : Fin n) (x : α) :
    DenseMatrix m n α where
  data := A.data.set (rowMajorIndex i j) x (rowMajorIndex_lt i j)

instance {m n : Nat} {α : Type u} [Inhabited α] [ToString α] : ToString (DenseMatrix m n α) where
  toString A := Id.run do
    let mut rows : Array String := #[]
    for i in [0:m] do
      let mut rowStr : Array String := #[]
      for j in [0:n] do
        -- Access the element using your existing `get!` function
        let val := A.get! i j
        rowStr := rowStr.push (toString val)
      -- Format the current row, e.g., "[1, 2, 3]"
      let rowFormatted := "![" ++ String.intercalate ", " rowStr.toList ++ "]"
      rows := rows.push rowFormatted
    -- Join all rows with a newline and a leading space for alignment
    return "![" ++ String.intercalate ", " rows.toList ++ "]"

/--
Convert a dense matrix to mathlib's function-backed matrix type.

`Matrix (Fin m) (Fin n) α` is represented extensionally as a function from row
and column indices to entries. The conversion exposes each dense entry through
`get`, preserving checked row-major access while hiding the underlying storage.
-/
def toMatrix {m n : Nat} {α : Type u} (A : DenseMatrix m n α) :
    Matrix (Fin m) (Fin n) α :=
  Matrix.of fun i j => A.get i j

/-- Reading the function-backed view is definitionally the checked dense read. -/
@[simp]
theorem toMatrix_apply {m n : Nat} {α : Type u}
    (A : DenseMatrix m n α) (i : Fin m) (j : Fin n) :
    A.toMatrix i j = A.get i j :=
  rfl

-- Flatten/unflatten arithmetic for row-major storage. Given a flat index
-- `x < m * n`, division by `n` recovers the row and modulo `n` recovers the
-- column. The modulo proof first rules out `n = 0`: otherwise `m * n = 0`,
-- contradicting the existence of such an `x`.

-- The quotient of a flat in-bounds index by the row width is a valid row
-- index.
private theorem index_div_lt {m n : Nat} {x : Nat} (h : x < m * n) : x / n < m := by
  rw [Nat.mul_comm] at h
  exact Nat.div_lt_of_lt_mul h

-- The remainder of a flat in-bounds index by the row width is a valid column
-- index.
private theorem index_mod_lt {m n : Nat} {x : Nat} (h : x < m * n) : x % n < n := by
  have hn : n ≠ 0 := by
    intro hn
    subst n
    simp at h
  exact Nat.mod_lt x (Nat.pos_of_ne_zero hn)

-- Flattening the row and column recovered from a flat index returns that index.
private theorem rowMajorIndex_unflatten {m n : Nat} (x : Fin (m * n)) :
    rowMajorIndex
        (m := m) (n := n)
        ⟨x.val / n, index_div_lt x.isLt⟩
        ⟨x.val % n, index_mod_lt x.isLt⟩ = x.val := by
  unfold rowMajorIndex
  rw [Nat.mul_comm (x.val / n) n, Nat.div_add_mod]

-- When a proof starts from typed indices `i : Fin m` and `j : Fin n`, the
-- witness `j` proves `n > 0`: `0 <= j.val < n`. That positivity is what lets
-- the division and modulo simplification lemmas recover `i.val` and `j.val`
-- from the flattened row-major offset.

-- Dividing a flattened typed row-major index by the row width recovers the
-- row.
private theorem rowMajorIndex_div {m n : Nat} (i : Fin m) (j : Fin n) :
    rowMajorIndex i j / n = i.val := by
  unfold rowMajorIndex
  rw [Nat.mul_comm i.val n]
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  rw [Nat.mul_add_div hn, Nat.div_eq_of_lt j.isLt, Nat.add_zero]

-- Taking a flattened typed row-major index modulo the row width recovers the
-- column.
private theorem rowMajorIndex_mod {m n : Nat} (i : Fin m) (j : Fin n) :
    rowMajorIndex i j % n = j.val := by
  unfold rowMajorIndex
  rw [Nat.mul_comm i.val n]
  rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt j.isLt]

/--
Build dense row-major storage from an entry function.

`Vector.ofFn` enumerates every flat slot exactly once. Each flat index is
unflattened as `(x / n, x % n)`, then the helper lemmas supply the typed row and
column bounds.
-/
def of {m n : Nat} {α : Type u} (f : Fin m → Fin n → α) : DenseMatrix m n α where
  data := Vector.ofFn fun x : Fin (m * n) =>
    f ⟨x.val / n, index_div_lt x.isLt⟩ ⟨x.val % n, index_mod_lt x.isLt⟩

@[simp]
theorem get_of {m n : Nat} {α : Type u}
    (f : Fin m → Fin n → α) (i : Fin m) (j : Fin n) :
    get (of f) i j = f i j := by
  simp [of, get, Vector.get, rowMajorIndex_div, rowMajorIndex_mod]

/--
Convert a function-backed matrix to row-major dense storage.

The executable path uses the native `DenseMatrix.of` builder; the source matrix
is read only to populate the dense backing vector.
-/
def ofMatrix {m n : Nat} {α : Type u} (M : Matrix (Fin m) (Fin n) α) :
    DenseMatrix m n α :=
  of fun i j => M i j

-- Reading a dense matrix built from a function-backed matrix returns the source
-- entry.
private theorem get_ofMatrix {m n : Nat} {α : Type u}
    (M : Matrix (Fin m) (Fin n) α) (i : Fin m) (j : Fin n) :
    get (ofMatrix M) i j = M i j := by
  simp [ofMatrix]

-- Reading storage through the unflattened row and column returns the same flat
-- slot.
private theorem get_unflatten {m n : Nat} {α : Type u}
    (data : Vector α (m * n)) (x : Fin (m * n)) :
    get { data := data }
        ⟨x.val / n, index_div_lt x.isLt⟩
        ⟨x.val % n, index_mod_lt x.isLt⟩ = data.get x := by
  have hflat :
      (⟨rowMajorIndex
          ⟨x.val / n, index_div_lt x.isLt⟩
          ⟨x.val % n, index_mod_lt x.isLt⟩,
        rowMajorIndex_lt
          ⟨x.val / n, index_div_lt x.isLt⟩
          ⟨x.val % n, index_mod_lt x.isLt⟩⟩ : Fin (m * n)) = x := by
    apply Fin.ext
    exact rowMajorIndex_unflatten x
  simp [get, hflat]

/--
Round trip from `Matrix` to `DenseMatrix` and back.

The proof is extensional in the row and column indices. After unfolding the two
conversions, the division and modulo helper lemmas show that reading the
row-major slot created for `(i, j)` returns exactly `M i j`.
-/
@[simp]
theorem toMatrix_ofMatrix {m n : Nat} {α : Type u} (M : Matrix (Fin m) (Fin n) α) :
    toMatrix (ofMatrix M) = M := by
  ext i j
  exact get_ofMatrix M i j

/--
Round trip from `DenseMatrix` to `Matrix` and back.

After destructing the dense matrix, it is enough to prove equality of the
backing vectors pointwise. The `get_unflatten` helper identifies each recreated
slot with the original flat slot.
-/
@[simp]
theorem ofMatrix_toMatrix {m n : Nat} {α : Type u} (A : DenseMatrix m n α) :
    ofMatrix (toMatrix A) = A := by
  cases A with
  | mk data =>
    rw [DenseMatrix.mk.injEq]
    apply Vector.ext
    intro x hx
    simp [ofMatrix, of, toMatrix, get_unflatten, Vector.get]

/-- Dense identity matrix built directly in row-major storage. -/
def identity {n : Nat} {α : Type u} [Zero α] [One α] : DenseMatrix n n α :=
  of fun i j => if i = j then 1 else 0

@[simp]
theorem get_identity {n : Nat} {α : Type u} [Zero α] [One α]
    (i j : Fin n) :
    get (identity : DenseMatrix n n α) i j = if i = j then 1 else 0 := by
  simp [identity]

@[simp]
theorem toMatrix_identity {n : Nat} {α : Type u} [Zero α] [One α] :
    toMatrix (identity : DenseMatrix n n α) = (1 : Matrix (Fin n) (Fin n) α) := by
  ext i j
  by_cases h : i = j <;> simp [identity, Matrix.one_apply, h]

/-
Pointwise dense arithmetic stays at the storage layer: `zipWith` and `map`
operate directly on the backing vector, and the bridge lemmas below recover the
usual Matrix-level interpretation entry by entry.
-/
def add {m n : Nat} {α : Type u} [Add α] (A B : DenseMatrix m n α) : DenseMatrix m n α where
  data := A.data.zipWith (· + ·) B.data

def smul {m n : Nat} {α : Type u} [Mul α] (c : α) (M : DenseMatrix m n α) : DenseMatrix m n α where
  data := M.data.map (fun x => c * x)

private theorem vector_get_zipWith {α β γ : Type u} {n : Nat}
    (f : α → β → γ) (a : Vector α n) (b : Vector β n) (i : Fin n) :
    (Vector.zipWith f a b).get i = f (a.get i) (b.get i) := by
  simp [Vector.get]

private theorem vector_get_map {α β : Type u} {n : Nat}
    (f : α → β) (a : Vector α n) (i : Fin n) :
    (Vector.map f a).get i = f (a.get i) := by
  simp [Vector.get]

@[simp]
theorem get_add {m n : Nat} {α : Type u} [Add α]
    (A B : DenseMatrix m n α) (i : Fin m) (j : Fin n) :
    get (add A B) i j = A.get i j + B.get i j := by
  simp [add, get, vector_get_zipWith]

@[simp]
theorem toMatrix_add {m n : Nat} {α : Type u} [Add α]
    (A B : DenseMatrix m n α) :
    toMatrix (add A B) = A.toMatrix + B.toMatrix := by
  ext i j
  simp

@[simp]
theorem get_smul {m n : Nat} {α : Type u} [Mul α]
    (c : α) (M : DenseMatrix m n α) (i : Fin m) (j : Fin n) :
    get (smul c M) i j = c * M.get i j := by
  simp [smul, get, vector_get_map]

@[simp]
theorem toMatrix_smul {m n : Nat} {α : Type u} [Mul α]
    (c : α) (M : DenseMatrix m n α) :
    toMatrix (smul c M) = Matrix.of (fun i j => c * M.toMatrix i j) := by
  ext i j
  simp

/-
Dense multiplication is intentionally executable first and proved correct
afterward.  `dot` accumulates one output entry, and `dot_eq_sum_Ico` connects
that tail-recursive accumulator to the finite sum used by mathlib's Matrix
multiplication.
-/
private def dot {m k n : Nat} {α : Type u} [Add α] [Mul α]
    (sum : α) (i : Fin m) (j : Fin n) (l : Fin k)
    (A : DenseMatrix m k α) (B : DenseMatrix k n α) : α :=
  if h: l + 1 < k then
    dot (sum + (A.get i l * B.get l j)) i j ⟨l+1, by simp [h]⟩ A B
  else
    sum + (A.get i l * B.get l j)

private theorem dot_eq_sum_Ico {m k n : Nat} {α : Type u} [AddCommMonoid α] [Mul α]
    (sum : α) (i : Fin m) (j : Fin n) (l : Fin k)
    (A : DenseMatrix m k α) (B : DenseMatrix k n α) :
    dot sum i j l A B =
      sum + ∑ x ∈ Finset.Ico l.val k,
        if h : x < k then A.get i ⟨x, h⟩ * B.get ⟨x, h⟩ j else 0 := by
  fun_induction dot sum i j l A B with
  | case1 sum l h ih =>
      rw [ih]
      have hlk : l.val < k := Nat.lt_trans (Nat.lt_succ_self l.val) h
      have hIco := Finset.sum_eq_sum_Ico_succ_bot (a := l.val) (b := k) hlk (fun x =>
        if hx : x < k then A.get i ⟨x, hx⟩ * B.get ⟨x, hx⟩ j else 0)
      rw [hIco]
      simp [add_assoc]
  | case2 sum l h =>
      let f : Nat → α := fun x =>
        if hx : x < k then A.get i ⟨x, hx⟩ * B.get ⟨x, hx⟩ j else 0
      have hmem : l.val ∈ Finset.Ico l.val k := by
        simp [l.isLt]
      have hzero : ∀ x ∈ Finset.Ico l.val k, x ≠ l.val → f x = 0 := by
        intro x hx hxne
        simp only [Finset.mem_Ico] at hx
        have hlt : l.val < x := Nat.lt_of_le_of_ne hx.1 (Ne.symm hxne)
        have hsucc : l.val + 1 ≤ x := Nat.succ_le_iff.mpr hlt
        have : l.val + 1 < k := Nat.lt_of_le_of_lt hsucc hx.2
        exact False.elim (h this)
      have hsum := Finset.sum_eq_single_of_mem l.val hmem hzero
      dsimp [f] at hsum
      rw [hsum]
      simp [l.isLt]

private theorem dot_zero_eq_matrix_mul_apply {m k n : Nat} {α : Type u}
    [AddCommMonoid α] [Mul α] [NeZero k]
    (i : Fin m) (j : Fin n) (A : DenseMatrix m k α) (B : DenseMatrix k n α) :
    dot 0 i j 0 A B = (A.toMatrix * B.toMatrix) i j := by
  rw [dot_eq_sum_Ico, Matrix.mul_apply]
  simp only [toMatrix_apply]
  have hsum :
      (∑ r : Fin k, A.get i r * B.get r j) =
        ∑ x ∈ Finset.range k,
          if hx : x < k then A.get i ⟨x, hx⟩ * B.get ⟨x, hx⟩ j else 0 := by
    calc
      (∑ r : Fin k, A.get i r * B.get r j) =
          ∑ r : Fin k,
            if hx : r.val < k then A.get i ⟨r.val, hx⟩ * B.get ⟨r.val, hx⟩ j else 0 := by
            simp
      _ = ∑ x ∈ Finset.range k,
          if hx : x < k then A.get i ⟨x, hx⟩ * B.get ⟨x, hx⟩ j else 0 := by
            exact Fin.sum_univ_eq_sum_range (fun x =>
              if hx : x < k then A.get i ⟨x, hx⟩ * B.get ⟨x, hx⟩ j else 0) k
  rw [hsum, Finset.range_eq_Ico]
  simp

/-
The multiplication helper writes the output vector from left to right in
row-major order.  The size lemmas are the small arithmetic facts that let Lean
see the next append either stays in the current row, starts the next row, or
finishes the `m * n` output slots.
-/
/-- If `i * n + j = out.size` and `j + 1 = n` then `(i + 1) * n = (out.push entry).size`. -/
private lemma row_size_invariant {α : Type u} (out : Array α) (i j n : Nat)
    (h_size : out.size = i * n + j) (hj : j + 1 = n) (entry : α)
    : (out.push entry).size = (i + 1) * n := by
  simp only [Array.size_push, h_size]
  suffices j + 1 = n from by grind
  exact hj

/-- The last `Array α` returned by `mul_helper` has size `m * n`. -/
private lemma mul_helper_size_invariant {m n : Nat} {α : Type u} (out : Array α) (i j : Nat)
    (h_size : out.size = i * n + j) (hi : i + 1 = m) (hj : j + 1 = n) (entry : α)
    : (out.push entry).size = m * n := by
  rw [Array.size_push, h_size, add_assoc, hj]
  nth_rewrite 2 [←one_mul n]
  rw [←right_distrib, hi]

/-- Computes entry ij of `A * B` and appends it to the resulting matrix. -/
private def mul_helper {m k n : Nat} {α : Type u} [Zero α] [Add α] [Mul α]
    [NeZero m] [NeZero k] [NeZero n]
    (out : Array α) (i j : Nat) (A : DenseMatrix m k α) (B : DenseMatrix k n α)
    (h_size : out.size = i * n + j) (hi : m ≥ i + 1) (hj : n ≥ j + 1)
    : Vector α (m * n) :=
  let entry := dot 0 ⟨i, by exact Nat.lt_of_succ_le hi⟩ ⟨j, by exact Nat.lt_of_succ_le hj⟩ 0 A B
  if h₁ : j + 1 < n then
    mul_helper (out.push entry) i (j+1) A B (by aesop) hi (by exact Nat.succ_le_of_lt h₁)
  else if h₂ : i + 1 < m then
    let hj' : j + 1 = n := by apply le_antisymm hj (by push Not at h₁; exact h₁)
    mul_helper (out.push entry) (i+1) 0 A B
      (row_size_invariant out i j n h_size hj' entry)
      (by exact Nat.succ_le_of_lt h₂) NeZero.one_le
  else
    let hi' : i + 1 = m := by apply le_antisymm hi (by push Not at h₂; exact h₂)
    let hj' : j + 1 = n := by apply le_antisymm hj (by push Not at h₁; exact h₁)
    ⟨out.push entry, mul_helper_size_invariant out i j h_size hi' hj' entry⟩

/-
The prefix predicate is the key correctness invariant for dense multiplication:
after each append, every already-written flat slot agrees with the corresponding
entry of `A.toMatrix * B.toMatrix`.  The final theorem reads that invariant back
through the completed vector.
-/
private def mulFlatEntry {m k n : Nat} {α : Type u} [AddCommMonoid α] [Mul α]
    (A : DenseMatrix m k α) (B : DenseMatrix k n α) (x : Fin (m * n)) : α :=
  (A.toMatrix * B.toMatrix)
    ⟨x.val / n, index_div_lt x.isLt⟩
    ⟨x.val % n, index_mod_lt x.isLt⟩

private def arrayMatchesMulPrefix {m k n : Nat} {α : Type u} [AddCommMonoid α] [Mul α]
    (out : Array α) (A : DenseMatrix m k α) (B : DenseMatrix k n α) : Prop :=
  ∀ x (hx_out : x < out.size) (hx_bound : x < m * n),
    out[x]'(hx_out) = mulFlatEntry A B ⟨x, hx_bound⟩

private theorem mul_current_index_lt {m n : Nat} {α : Type u}
    (out : Array α) (i j : Nat)
    (h_size : out.size = i * n + j) (hi : m ≥ i + 1) (hj : n ≥ j + 1) :
    out.size < m * n := by
  have hi_lt : i < m := Nat.lt_of_succ_le hi
  have hj_lt : j < n := Nat.lt_of_succ_le hj
  rw [h_size]
  simpa [rowMajorIndex] using
    rowMajorIndex_lt (m := m) (n := n) ⟨i, hi_lt⟩ ⟨j, hj_lt⟩

private theorem mul_current_entry_eq_flat {m k n : Nat} {α : Type u}
    [AddCommMonoid α] [Mul α] [NeZero k]
    (out : Array α) (i j : Nat) (A : DenseMatrix m k α) (B : DenseMatrix k n α)
    (h_size : out.size = i * n + j) (hi : m ≥ i + 1) (hj : n ≥ j + 1)
    (h_bound : out.size < m * n) :
    dot 0 ⟨i, Nat.lt_of_succ_le hi⟩ ⟨j, Nat.lt_of_succ_le hj⟩ 0 A B =
      mulFlatEntry A B ⟨out.size, h_bound⟩ := by
  have hi_lt : i < m := Nat.lt_of_succ_le hi
  have hj_lt : j < n := Nat.lt_of_succ_le hj
  have hdiv : out.size / n = i := by
    rw [h_size]
    simpa [rowMajorIndex] using
      rowMajorIndex_div (m := m) (n := n) ⟨i, hi_lt⟩ ⟨j, hj_lt⟩
  have hmod : out.size % n = j := by
    rw [h_size]
    simpa [rowMajorIndex] using
      rowMajorIndex_mod (m := m) (n := n) ⟨i, hi_lt⟩ ⟨j, hj_lt⟩
  simpa [mulFlatEntry, hdiv, hmod] using
    dot_zero_eq_matrix_mul_apply
      (i := ⟨i, hi_lt⟩) (j := ⟨j, hj_lt⟩) A B

private theorem arrayMatchesMulPrefix_push {m k n : Nat} {α : Type u}
    [AddCommMonoid α] [Mul α]
    {out : Array α} {entry : α} {A : DenseMatrix m k α} {B : DenseMatrix k n α}
    (h_out : arrayMatchesMulPrefix out A B) (h_bound : out.size < m * n)
    (h_entry : entry = mulFlatEntry A B ⟨out.size, h_bound⟩) :
    arrayMatchesMulPrefix (out.push entry) A B := by
  intro x hx_push hx_bound
  by_cases hx_out : x < out.size
  · simpa [Array.getElem_push_lt hx_out] using h_out x hx_out hx_bound
  · have hx_le : x ≤ out.size := Nat.le_of_lt_succ (by simpa [Array.size_push] using hx_push)
    have hx_ge : out.size ≤ x := Nat.le_of_not_gt hx_out
    have hx_eq : x = out.size := le_antisymm hx_le hx_ge
    subst x
    simpa [Array.getElem_push_eq] using h_entry

private theorem mul_helper_get_flat {m k n : Nat} {α : Type u}
    [AddCommMonoid α] [Mul α] [NeZero m] [NeZero k] [NeZero n]
    (out : Array α) (i j : Nat) (A : DenseMatrix m k α) (B : DenseMatrix k n α)
    (h_size : out.size = i * n + j) (hi : m ≥ i + 1) (hj : n ≥ j + 1)
    (h_out : arrayMatchesMulPrefix out A B) (x : Fin (m * n)) :
    (mul_helper out i j A B h_size hi hj).get x = mulFlatEntry A B x := by
  fun_induction mul_helper out i j A B h_size hi hj with
  | case1 out i j h_size hi hj entry h ih =>
      have h_bound : out.size < m * n :=
        mul_current_index_lt out i j h_size hi hj
      have h_entry : entry = mulFlatEntry A B ⟨out.size, h_bound⟩ := by
        simpa [entry] using
          mul_current_entry_eq_flat out i j A B h_size hi hj h_bound
      exact ih (arrayMatchesMulPrefix_push h_out h_bound h_entry)
  | case2 out i j h_size hi hj entry h₁ h₂ hj' ih =>
      have h_bound : out.size < m * n :=
        mul_current_index_lt out i j h_size hi hj
      have h_entry : entry = mulFlatEntry A B ⟨out.size, h_bound⟩ := by
        simpa [entry] using
          mul_current_entry_eq_flat out i j A B h_size hi hj h_bound
      exact ih (arrayMatchesMulPrefix_push h_out h_bound h_entry)
  | case3 out i j h_size hi hj entry h₁ h₂ hi' hj' =>
      have h_bound : out.size < m * n :=
        mul_current_index_lt out i j h_size hi hj
      have h_entry : entry = mulFlatEntry A B ⟨out.size, h_bound⟩ := by
        simpa [entry] using
          mul_current_entry_eq_flat out i j A B h_size hi hj h_bound
      have h_push := arrayMatchesMulPrefix_push h_out h_bound h_entry
      have hx : x.val < (out.push entry).size := by
        rw [mul_helper_size_invariant out i j h_size hi' hj' entry]
        exact x.isLt
      simpa [Vector.get] using h_push x.val hx x.isLt

/--
Optimized dense matrix multiplication for nonempty dimensions.

This path builds the output storage sequentially and computes each dot product
with checked dense reads. It requires `[NeZero m] [NeZero k] [NeZero n]` so the
recursive helper can start at row, column, and dot-product index `0`.
-/
def mul {m k n : Nat} {α : Type u} [Inhabited α] [Zero α] [Add α] [Mul α]
    [NeZero m] [NeZero k] [NeZero n]
    (A : DenseMatrix m k α) (B : DenseMatrix k n α) : DenseMatrix m n α where
  data := mul_helper (Array.mkEmpty (m * n)) 0 0 A B (by simp) NeZero.one_le NeZero.one_le

@[simp]
theorem get_mul {m k n : Nat} {α : Type u} [Inhabited α] [AddCommMonoid α] [Mul α]
    [NeZero m] [NeZero k] [NeZero n]
    (A : DenseMatrix m k α) (B : DenseMatrix k n α) (i : Fin m) (j : Fin n) :
    get (mul A B) i j = (A.toMatrix * B.toMatrix) i j := by
  let x : Fin (m * n) := ⟨rowMajorIndex i j, rowMajorIndex_lt i j⟩
  have h_prefix : arrayMatchesMulPrefix (Array.mkEmpty (m * n)) A B := by
    intro y hy
    simp at hy
  have h_get :
      (mul_helper (Array.mkEmpty (m * n)) 0 0 A B (by simp) NeZero.one_le NeZero.one_le).get x =
        mulFlatEntry A B x :=
    mul_helper_get_flat (Array.mkEmpty (m * n)) 0 0 A B
      (by simp) NeZero.one_le NeZero.one_le h_prefix x
  have hdiv : x.val / n = i.val := by
    simpa [x] using rowMajorIndex_div (m := m) (n := n) i j
  have hmod : x.val % n = j.val := by
    simpa [x] using rowMajorIndex_mod (m := m) (n := n) i j
  simpa [mul, get, x, mulFlatEntry, hdiv, hmod] using h_get

@[simp]
theorem toMatrix_mul {m k n : Nat} {α : Type u} [Inhabited α] [AddCommMonoid α] [Mul α]
    [NeZero m] [NeZero k] [NeZero n]
    (A : DenseMatrix m k α) (B : DenseMatrix k n α) :
    toMatrix (mul A B) = A.toMatrix * B.toMatrix := by
  ext i j
  simp

/-
Transpose uses the same sequential-array strategy as multiplication, but the
target storage is `n * m` and a flat output index decodes as `(column, row)` of
the source.  Keeping the proof parallel to multiplication makes the row-major
invariant explicit instead of relying on opaque array equality.
-/
/-- The last `Array α` returned by `transpose_helper` has size `n * m`. -/
private lemma transpose_helper_size_invariant {m n : Nat} {α : Type u} (out : Array α) (i j : Nat)
    (h_size : out.size = j * m + i) (hi : i + 1 = m) (hj : j + 1 = n) (entry : α)
    : (out.push entry).size = n * m := by
  rw [Array.size_push, h_size, add_assoc, hi]
  nth_rewrite 2 [←one_mul m]
  rw [←right_distrib, hj]

/-- Computes entry `ij` of M.T and appends it to the resulting matrix. -/
private def transpose_helper {m n : Nat} {α : Type u} [NeZero m] [NeZero n]
    (out : Array α) (i j : Nat) (M : DenseMatrix m n α)
    (h_size : out.size = j * m + i) (hi : m ≥ i + 1) (hj : n ≥ j + 1)
    :  Vector α (n * m) :=
  let entry := M.get ⟨i, by exact Nat.lt_of_succ_le hi⟩ ⟨j, by exact Nat.lt_of_succ_le hj⟩
  if h₁ : i + 1 < m then
    transpose_helper (out.push entry) (i+1) j M (by aesop) (by exact Nat.succ_le_of_lt h₁) hj
  else if h₂ : j + 1 < n then
    let hj' : i + 1 = m := by apply le_antisymm hi (by push Not at h₁; exact h₁)
    transpose_helper (out.push entry) 0 (j+1) M
      (row_size_invariant out j i m h_size hj' entry)
      NeZero.one_le (by exact Nat.succ_le_of_lt h₂)
  else
    let hi' : i + 1 = m := by apply le_antisymm hi (by push Not at h₁; exact h₁)
    let hj' : j + 1 = n := by apply le_antisymm hj (by push Not at h₂; exact h₂)
    ⟨out.push entry, transpose_helper_size_invariant out i j h_size hi' hj' entry⟩

/-
Flat transpose entries decode an output slot as a source column and row.  The
prefix proof below uses this as the specification for every array slot already
written by `transpose_helper`.
-/
private def transposeFlatEntry {m n : Nat} {α : Type u}
    (M : DenseMatrix m n α) (x : Fin (n * m)) : α :=
  M.toMatrix
    ⟨x.val % m, index_mod_lt (m := n) (n := m) x.isLt⟩
    ⟨x.val / m, index_div_lt (m := n) (n := m) x.isLt⟩

private def arrayMatchesTransposePrefix {m n : Nat} {α : Type u}
    (out : Array α) (M : DenseMatrix m n α) : Prop :=
  ∀ x (hx_out : x < out.size) (hx_bound : x < n * m),
    out[x]'(hx_out) = transposeFlatEntry M ⟨x, hx_bound⟩

private theorem transpose_current_index_lt {m n : Nat} {α : Type u}
    (out : Array α) (i j : Nat)
    (h_size : out.size = j * m + i) (hi : m ≥ i + 1) (hj : n ≥ j + 1) :
    out.size < n * m := by
  have hi_lt : i < m := Nat.lt_of_succ_le hi
  have hj_lt : j < n := Nat.lt_of_succ_le hj
  rw [h_size]
  simpa [rowMajorIndex] using
    rowMajorIndex_lt (m := n) (n := m) ⟨j, hj_lt⟩ ⟨i, hi_lt⟩

private theorem transpose_current_entry_eq_flat {m n : Nat} {α : Type u}
    (out : Array α) (i j : Nat) (M : DenseMatrix m n α)
    (h_size : out.size = j * m + i) (hi : m ≥ i + 1) (hj : n ≥ j + 1)
    (h_bound : out.size < n * m) :
    M.get ⟨i, Nat.lt_of_succ_le hi⟩ ⟨j, Nat.lt_of_succ_le hj⟩ =
      transposeFlatEntry M ⟨out.size, h_bound⟩ := by
  have hi_lt : i < m := Nat.lt_of_succ_le hi
  have hj_lt : j < n := Nat.lt_of_succ_le hj
  have hdiv : out.size / m = j := by
    rw [h_size]
    simpa [rowMajorIndex] using
      rowMajorIndex_div (m := n) (n := m) ⟨j, hj_lt⟩ ⟨i, hi_lt⟩
  have hmod : out.size % m = i := by
    rw [h_size]
    simpa [rowMajorIndex] using
      rowMajorIndex_mod (m := n) (n := m) ⟨j, hj_lt⟩ ⟨i, hi_lt⟩
  simp [transposeFlatEntry, hdiv, hmod]

private theorem arrayMatchesTransposePrefix_push {m n : Nat} {α : Type u}
    {out : Array α} {entry : α} {M : DenseMatrix m n α}
    (h_out : arrayMatchesTransposePrefix out M) (h_bound : out.size < n * m)
    (h_entry : entry = transposeFlatEntry M ⟨out.size, h_bound⟩) :
    arrayMatchesTransposePrefix (out.push entry) M := by
  intro x hx_push hx_bound
  by_cases hx_out : x < out.size
  · simpa [Array.getElem_push_lt hx_out] using h_out x hx_out hx_bound
  · have hx_le : x ≤ out.size := Nat.le_of_lt_succ (by simpa [Array.size_push] using hx_push)
    have hx_ge : out.size ≤ x := Nat.le_of_not_gt hx_out
    have hx_eq : x = out.size := le_antisymm hx_le hx_ge
    subst x
    simpa [Array.getElem_push_eq] using h_entry

private theorem transpose_helper_get_flat {m n : Nat} {α : Type u} [NeZero m] [NeZero n]
    (out : Array α) (i j : Nat) (M : DenseMatrix m n α)
    (h_size : out.size = j * m + i) (hi : m ≥ i + 1) (hj : n ≥ j + 1)
    (h_out : arrayMatchesTransposePrefix out M) (x : Fin (n * m)) :
    (transpose_helper out i j M h_size hi hj).get x = transposeFlatEntry M x := by
  fun_induction transpose_helper out i j M h_size hi hj with
  | case1 out i j h_size hi hj entry h ih =>
      have h_bound : out.size < n * m :=
        transpose_current_index_lt out i j h_size hi hj
      have h_entry : entry = transposeFlatEntry M ⟨out.size, h_bound⟩ := by
        simpa [entry] using
          transpose_current_entry_eq_flat out i j M h_size hi hj h_bound
      exact ih (arrayMatchesTransposePrefix_push h_out h_bound h_entry)
  | case2 out i j h_size hi hj entry h₁ h₂ hi' ih =>
      have h_bound : out.size < n * m :=
        transpose_current_index_lt out i j h_size hi hj
      have h_entry : entry = transposeFlatEntry M ⟨out.size, h_bound⟩ := by
        simpa [entry] using
          transpose_current_entry_eq_flat out i j M h_size hi hj h_bound
      exact ih (arrayMatchesTransposePrefix_push h_out h_bound h_entry)
  | case3 out i j h_size hi hj entry h₁ h₂ hi' hj' =>
      have h_bound : out.size < n * m :=
        transpose_current_index_lt out i j h_size hi hj
      have h_entry : entry = transposeFlatEntry M ⟨out.size, h_bound⟩ := by
        simpa [entry] using
          transpose_current_entry_eq_flat out i j M h_size hi hj h_bound
      have h_push := arrayMatchesTransposePrefix_push h_out h_bound h_entry
      have hx : x.val < (out.push entry).size := by
        rw [transpose_helper_size_invariant out i j h_size hi' hj' entry]
        exact x.isLt
      simpa [Vector.get] using h_push x.val hx x.isLt

/-- Dense transpose built by writing the transposed row-major storage directly. -/
def transpose {m n : Nat} {α : Type u} [NeZero m] [NeZero n]
    (M : DenseMatrix m n α) : DenseMatrix n m α :=
  { data := transpose_helper (Array.mkEmpty (n * m)) 0 0 M (by simp) NeZero.one_le NeZero.one_le }

@[simp]
theorem get_transpose {m n : Nat} {α : Type u} [NeZero m] [NeZero n]
    (M : DenseMatrix m n α) (i : Fin n) (j : Fin m) :
    get (transpose M) i j = M.get j i := by
  let x : Fin (n * m) := ⟨rowMajorIndex i j, rowMajorIndex_lt i j⟩
  have h_prefix : arrayMatchesTransposePrefix (Array.mkEmpty (n * m)) M := by
    intro y hy
    simp at hy
  have h_get :
      (transpose_helper (Array.mkEmpty (n * m)) 0 0 M (by simp) NeZero.one_le NeZero.one_le).get x =
        transposeFlatEntry M x :=
    transpose_helper_get_flat (Array.mkEmpty (n * m)) 0 0 M
      (by simp) NeZero.one_le NeZero.one_le h_prefix x
  have hdiv : x.val / m = i.val := by
    simpa [x] using rowMajorIndex_div (m := n) (n := m) i j
  have hmod : x.val % m = j.val := by
    simpa [x] using rowMajorIndex_mod (m := n) (n := m) i j
  simpa [transpose, get, x, transposeFlatEntry, hdiv, hmod] using h_get

@[simp]
theorem toMatrix_transpose {m n : Nat} {α : Type u} [NeZero m] [NeZero n]
    (M : DenseMatrix m n α) :
    toMatrix (transpose M) = M.toMatrix.transpose := by
  ext i j
  simp

end DenseMatrix
