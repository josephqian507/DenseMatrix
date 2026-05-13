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
Read an entry using checked row-major indexing.

The value-level index is computed by `rowMajorIndex`; the paired proof
`rowMajorIndex_lt` turns that offset into a `Fin (m * n)`. Thus `get` has no
unchecked fallback and no default value.
-/
def get {m n : Nat} {α : Type u} (A : DenseMatrix m n α) (i : Fin m) (j : Fin n) : α :=
  A.data.get ⟨rowMajorIndex i j, rowMajorIndex_lt i j⟩

/--
Return a matrix with one entry updated.

The update uses the same checked row-major offset as `get`; the `Vector` result
keeps the same length by construction.
-/
def set {m n : Nat} {α : Type u} (A : DenseMatrix m n α) (i : Fin m) (j : Fin n) (x : α) :
    DenseMatrix m n α where
  data := A.data.set (rowMajorIndex i j) x (rowMajorIndex_lt i j)

/--
Convert a dense matrix to mathlib's function-backed matrix type.

`Matrix (Fin m) (Fin n) α` is represented extensionally as a function from row
and column indices to entries. The conversion exposes each dense entry through
`get`, preserving checked row-major access while hiding the underlying storage.
-/
def toMatrix {m n : Nat} {α : Type u} (A : DenseMatrix m n α) :
    Matrix (Fin m) (Fin n) α :=
  Matrix.of fun i j => A.get i j

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
Convert a function-backed matrix to row-major dense storage.

`Vector.ofFn` enumerates every `x : Fin (m * n)` exactly once. Each flat index
is unflattened as `(x / n, x % n)`, then the helper lemmas supply the `Fin m`
and `Fin n` bounds.
-/
def ofMatrix {m n : Nat} {α : Type u} (M : Matrix (Fin m) (Fin n) α) :
    DenseMatrix m n α where
  data := Vector.ofFn fun x : Fin (m * n) =>
    M ⟨x.val / n, index_div_lt x.isLt⟩ ⟨x.val % n, index_mod_lt x.isLt⟩

-- Reading a dense matrix built from a function-backed matrix returns the source
-- entry.
private theorem get_ofMatrix {m n : Nat} {α : Type u}
    (M : Matrix (Fin m) (Fin n) α) (i : Fin m) (j : Fin n) :
    get (ofMatrix M) i j = M i j := by
  simp [ofMatrix, get, Vector.get, rowMajorIndex_div, rowMajorIndex_mod]

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
    simp [ofMatrix, toMatrix, get_unflatten, Vector.get]

end DenseMatrix
