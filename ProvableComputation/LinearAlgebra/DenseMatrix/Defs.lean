import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Dense matrix basics

This file contains only the minimal Vector-backed representation for dense
matrices and the bridge to mathlib's function-backed `Matrix` type.

The dimensions are tracked by the storage type itself: a value of
`DenseMatrix m n α` stores exactly `m * n` entries in one `Vector α (m * n)`.
Entries are flattened in row-major order, so row `i`, column `j` lives at offset
`i * n + j`.
-/

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
Flatten/unflatten arithmetic for row-major storage. Given a flat index
 `x < m * n`, division by `n` recovers the row and modulo `n` recovers the
column. The modulo proof first rules out `n = 0`: otherwise `m * n = 0`,
contradicting the existence of such an `x`.

The quotient of a flat in-bounds index by the row width is a valid row
index.
-/
theorem index_div_lt {m n : Nat} {x : Nat} (h : x < m * n) : x / n < m := by
  rw [Nat.mul_comm] at h
  exact Nat.div_lt_of_lt_mul h

/--
The remainder of a flat in-bounds index by the row width is a valid column
index.
-/
theorem index_mod_lt {m n : Nat} {x : Nat} (h : x < m * n) : x % n < n := by
  have hn : n ≠ 0 := by
    intro hn
    subst n
    simp at h
  exact Nat.mod_lt x (Nat.pos_of_ne_zero hn)

/-- Flattening the row and column recovered from a flat index returns that index. -/
private theorem rowMajorIndex_unflatten {m n : Nat} (x : Fin (m * n)) :
    rowMajorIndex
        (m := m) (n := n)
        ⟨x.val / n, index_div_lt x.isLt⟩
        ⟨x.val % n, index_mod_lt x.isLt⟩ = x.val := by
  unfold rowMajorIndex
  rw [Nat.mul_comm (x.val / n) n, Nat.div_add_mod]

/--
When a proof starts from typed indices `i : Fin m` and `j : Fin n`, the
witness `j` proves `n > 0`: `0 <= j.val < n`. That positivity is what lets
the division and modulo simplification lemmas recover `i.val` and `j.val`
from the flattened row-major offset.

Dividing a flattened typed row-major index by the row width recovers the
row.
-/
private theorem rowMajorIndex_div {m n : Nat} (i : Fin m) (j : Fin n) :
    rowMajorIndex i j / n = i.val := by
  unfold rowMajorIndex
  rw [Nat.mul_comm i.val n]
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  rw [Nat.mul_add_div hn, Nat.div_eq_of_lt j.isLt, Nat.add_zero]

/-- Taking a flattened typed row-major index modulo the row width recovers the column. -/
private theorem rowMajorIndex_mod {m n : Nat} (i : Fin m) (j : Fin n) :
    rowMajorIndex i j % n = j.val := by
  unfold rowMajorIndex
  rw [Nat.mul_comm i.val n]
  rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt j.isLt]

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

-- ToString instance
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

/--
Convert a function-backed matrix to row-major dense storage.

`Vector.ofFn` enumerates every `x : Fin (m * n)` exactly once. Each flat index
is unflattened as `(x / n, x % n)`, then the helper lemmas supply the `Fin m`
and `Fin n` bounds.

Note: `ofMatrix` is computationally expensive due to division, use sparingly.
-/
def ofMatrix {m n : Nat} {α : Type u} (M : Matrix (Fin m) (Fin n) α) :
    DenseMatrix m n α where
  data := Vector.ofFn fun x : Fin (m * n) =>
    M ⟨x.val / n, index_div_lt x.isLt⟩ ⟨x.val % n, index_mod_lt x.isLt⟩

-- Reading a dense matrix built from a function-backed matrix returns the source
-- entry.
theorem get_ofMatrix {m n : Nat} {α : Type u}
    (M : Matrix (Fin m) (Fin n) α) (i : Fin m) (j : Fin n) :
    get (ofMatrix M) i j = M i j := by
  simp [ofMatrix, get, Vector.get, rowMajorIndex_div, rowMajorIndex_mod]

-- TODO: fill in sorry
theorem get_toMatrix {m n : Nat} {α : Type u} (A : DenseMatrix m n α) (i : Fin m) (j : Fin n)
    : (toMatrix A) i j = get A i j := by
  sorry

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

/-- Define a `DenseMatrix` using a function.

Note: `DenseMatrix.of f` is equivalent to `DenseMatrix.ofMatrix (Matrix.of f)`.
-/
def of {m n : Nat} {α : Type u} (f : Fin m → Fin n → α) : DenseMatrix m n α :=
  .ofMatrix (Matrix.of f)

def add {m n : Nat} {α : Type u} [Add α] (A B : DenseMatrix m n α) : DenseMatrix m n α where
  data := A.data.zipWith (· + ·) B.data

instance {m n : Nat} {α : Type u} [Add α] : Add (DenseMatrix m n α) := ⟨add⟩

theorem add_ofMatrix {m n : Nat} {α : Type u} [Add α] (A B : Matrix (Fin m) (Fin n) α)
    : add (ofMatrix A) (ofMatrix B) = ofMatrix (A + B) := by
  rw [add, DenseMatrix.mk.injEq]
  apply Vector.ext
  intro x hx
  simp [ofMatrix]

theorem add_toMatrix {m n : Nat} {α : Type u} [Add α] (A B : DenseMatrix m n α)
    : toMatrix (add A B) = (toMatrix A) + (toMatrix B) := by
  let M := toMatrix A
  let N := toMatrix B
  suffices ofMatrix (toMatrix (add (ofMatrix M) (ofMatrix N)))
    = ofMatrix ((toMatrix (ofMatrix M)) + (toMatrix (ofMatrix N))) from by aesop
  rw [ofMatrix_toMatrix, toMatrix_ofMatrix, toMatrix_ofMatrix]
  exact add_ofMatrix M N

-- TODO: Check if this is faster than mathlib Matrix.smul
def smul {m n : Nat} {α : Type u} [Mul α] (c : α) (M : DenseMatrix m n α) : DenseMatrix m n α where
  data := M.data.map (fun x => c * x)

-- TODO: (benchmarking) compare efficiency of `dot` and `sum_dot`.
/--
Given indices `i` and `j`, returns the dot product of the i-th row of `A` and the j-th column
of `B `.

Note: dot products are defined for function-backed vector representation in Mathlib.Data.Matrix.Mul.
-/
private def dot {m k n : Nat} {α : Type u} [Add α] [Mul α]
    (sum : α) (i : Fin m) (j : Fin n) (l : Fin k)
    (A : DenseMatrix m k α) (B : DenseMatrix k n α) : α :=
  if h: l + 1 < k then
    dot (sum + (A.get i l * B.get l j)) i j ⟨l+1, by simp [h]⟩ A B
  else
    sum + (A.get i l * B.get l j)

private def sum_dot {m k n : Nat} {α : Type u} [Semiring α]
    (i : Fin m) (j : Fin n) (A : DenseMatrix m k α) (B : DenseMatrix k n α) : α :=
  ∑ l : Fin k, A.get i l * B.get l j

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

instance {m k n : Nat} {α : Type u} [Inhabited α] [Zero α] [Add α] [Mul α]
  [NeZero m] [NeZero k] [NeZero n]
  : HMul (DenseMatrix m k α) (DenseMatrix k n α) (DenseMatrix m n α) := ⟨mul⟩

/- --- Step 1: Characterize the `dot` accumulator loop --- -/
private theorem dot_eq_sum_plus {m k n : Nat} {α : Type u} [Semiring α]
    (sum : α) (i : Fin m) (j : Fin n) (l : Fin k)
    (A : DenseMatrix m k α) (B : DenseMatrix k n α) :
    dot sum i j l A B = sum + ∑ x : Fin k, if x ≥ l then A.get i x * B.get x j else 0 := by
  -- We prove this by well-founded induction on the remaining distance `k - l.val`
  induction h_step : k - l.val generalizing l sum with
  | zero =>
    omega
  | succ =>
    rename_i n ih
    unfold dot
    have h_next : k - (l.val + 1) = n := by omega
    split_ifs with h₁
    · rw [ih (sum + A.get i l * B.get l j) ⟨l + 1, h₁⟩ h_next]
      rw [add_assoc]
      congr 1
      sorry
    · push Not at h₁
      have h_step : k ≥ l + 1 := by omega
      have h₁ : k = l + 1 := by apply le_antisymm h₁ h_step
      sorry -- Standard structural induction / termination-based proof on `k - l`

/-- Core specification lemma for `dot` starting at 0 -/
private theorem dot_zero_eq_matrix_mul {m k n : Nat} {α : Type u} [Semiring α] [NeZero k]
    (i : Fin m) (j : Fin n) (A : DenseMatrix m k α) (B : DenseMatrix k n α) :
    dot 0 i j 0 A B = ∑ l : Fin k, A.get i l * B.get l j := by
  rw [dot_eq_sum_plus 0 i j 0 A B, zero_add]
  congr 1

/- --- Step 2: Characterize the flat array building loop --- -/
private theorem mul_helper_spec {m k n : Nat} {α : Type u} [Semiring α] [Inhabited α]
    [NeZero m] [NeZero k] [NeZero n]
    (out : Array α) (i j : Nat) (A : DenseMatrix m k α) (B : DenseMatrix k n α)
    (h_size : out.size = i * n + j) (hi : m ≥ i + 1) (hj : n ≥ j + 1)
    (h_out : ∀ (idx : Fin (m * n)), (h_idx : idx.val < out.size) →
      out[idx.val]'h_idx =
      ∑ l : Fin k,
      (A.get ⟨idx.val / n, index_div_lt idx.isLt⟩ l * B.get l ⟨idx.val % n, index_mod_lt idx.isLt⟩))
    : (mul_helper out i j A B h_size hi hj) =
    Vector.ofFn (fun x : Fin (m * n) => ∑ l : Fin k,
    (A.get ⟨x.val / n, index_div_lt x.isLt⟩ l * B.get l ⟨x.val % n, index_mod_lt x.isLt⟩)) := by
  unfold mul_helper
  dsimp only
  have h_entry : dot 0 ⟨i, Nat.lt_of_succ_le hi⟩ ⟨j, Nat.lt_of_succ_le hj⟩ 0 A B =
      ∑ l : Fin k, A.get ⟨i, Nat.lt_of_succ_le hi⟩ l * B.get l ⟨j, Nat.lt_of_succ_le hj⟩ := by
    exact dot_zero_eq_matrix_mul ⟨i, _⟩ ⟨j, _⟩ A B
  simp only [h_entry]
  split
  · rename_i h₁
    -- Case 1: Next column in the same row (j + 1 < n)
    have h_size' : (out.push
      (∑ l : Fin k, A.get ⟨i, by exact hi⟩ l * B.get l ⟨j, by exact hj⟩)).size
      = i * n + (j + 1) := by
      rw [Array.size_push, h_size, Nat.add_assoc]
    apply mul_helper_spec (out.push _) i (j + 1) A B h_size' hi (Nat.succ_le_of_lt h₁)
    intro idx h_lt
    rw [Array.size_push] at h_lt
    by_cases h_old : idx.val < out.size
    · rw [Array.getElem_push_lt h_old]
      exact h_out idx h_old
    · have h_eq_size : idx.val = out.size := by omega
      simp only [h_eq_size, Array.getElem_push_eq]
      have h_out' : out.size = rowMajorIndex ⟨i, by exact hi⟩ ⟨j, by exact hj⟩ := by
        rw [h_size, rowMajorIndex]
      have h_div : out.size / n = i := by rw [h_out', rowMajorIndex_div]
      have h_mod : out.size % n = j := by rw [h_out', rowMajorIndex_mod]
      simp [h_div, h_mod]
  · rename_i h_not_₁
    split
    · rename_i h₂
      -- Case 2: Row overflow, wrap to next row (¬(j + 1 < n) ∧ i + 1 < m)
      have hj' : j + 1 = n := by omega
      have h_size' := row_size_invariant out i j n h_size hj'
        (∑ l : Fin k, A.get ⟨i, by exact hi⟩ l * B.get l ⟨j, by exact hj⟩)
      apply mul_helper_spec (out.push _) (i + 1) 0 A B h_size' (Nat.succ_le_of_lt h₂) NeZero.one_le
      intro idx h_lt
      rw [Array.size_push] at h_lt
      by_cases h_old : idx.val < out.size
      · rw [Array.getElem_push_lt h_old]
        exact h_out idx h_old
      · have h_eq_size : idx.val = out.size := by omega
        simp only [h_eq_size, Array.getElem_push_eq]
        have h_out' : out.size = rowMajorIndex ⟨i, by exact hi⟩ ⟨j, by exact hj⟩ := by
          rw [h_size, rowMajorIndex]
        have h_div : out.size / n = i := by rw [h_out', rowMajorIndex_div]
        have h_mod : out.size % n = j := by rw [h_out', rowMajorIndex_mod]
        simp [h_div, h_mod]
    · rename_i h_not_₂
      -- Case 3: Base Case (End of Matrix)
      have hi' : i + 1 = m := by omega
      have hj' : j + 1 = n := by omega
      apply Vector.ext
      intro x hx
      rw [Vector.ofFn]
      simp only [Vector.getElem_mk, Array.getElem_ofFn]
      by_cases h_old : x < out.size
      · simp only [Array.getElem_push_lt h_old]
        exact h_out ⟨x, hx⟩ h_old
      · have h_eq_size : x = out.size := by
          have hx' : x < out.size + 1 := by
            rw [h_size, add_assoc, hj']
            nth_rewrite 2 [←one_mul n]
            rw [←add_mul, hi']
            exact hx
          omega
        simp only [h_eq_size, Array.getElem_push_eq]
        have h_out' : out.size = rowMajorIndex ⟨i, by exact hi⟩ ⟨j, by exact hj⟩ := by
          rw [h_size, rowMajorIndex]
        have h_div : x / n = i := by rw [h_eq_size, h_out', rowMajorIndex_div]
        have h_mod : x % n = j := by rw [h_eq_size, h_out', rowMajorIndex_mod]
        simp [←h_eq_size, h_div, h_mod]

theorem mul_ofMatrix {m k n : Nat} {α : Type u} [Semiring α] [Inhabited α]
    [NeZero m] [NeZero k] [NeZero n] (A : Matrix (Fin m) (Fin k) α) (B : Matrix (Fin k) (Fin n) α)
    : mul (ofMatrix A) (ofMatrix B) = ofMatrix (A * B : Matrix (Fin m) (Fin n) α) := by
  rw [mul, DenseMatrix.mk.injEq]
  have h_spec := mul_helper_spec (Array.mkEmpty (m * n)) 0 0 (ofMatrix A) (ofMatrix B) (by simp)
    NeZero.one_le NeZero.one_le (by simp)
  apply Vector.ext
  intro i x
  rw [h_spec]
  nth_rewrite 3 [ofMatrix]
  simp only [Vector.getElem_ofFn, Matrix.mul_apply, get_ofMatrix]

theorem mul_toMatrix {m k n : Nat} {α : Type u} [Semiring α] [Inhabited α]
    [NeZero m] [NeZero k] [NeZero n] (A : DenseMatrix m k α) (B : DenseMatrix k n α)
    : toMatrix (mul A B) = (toMatrix A) * (toMatrix B) := by
  let M := toMatrix A
  let N := toMatrix B
  suffices ofMatrix (toMatrix (mul (ofMatrix M) (ofMatrix N)))
    = ofMatrix ((toMatrix (ofMatrix M)) * (toMatrix (ofMatrix N))) from by aesop
  rw [ofMatrix_toMatrix, toMatrix_ofMatrix, toMatrix_ofMatrix]
  exact mul_ofMatrix M N

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

def transpose {m n : Nat} {α : Type u} [NeZero m] [NeZero n]
    (M : DenseMatrix m n α) : DenseMatrix n m α :=
  { data := transpose_helper (Array.mkEmpty (n * m)) 0 0 M (by simp) NeZero.one_le NeZero.one_le }

/-- Swap two rows of a dense matrix. -/
def swapRow {m n : Nat} {α : Type u}
    (A : DenseMatrix m n α) (r1 r2 : Fin m) : DenseMatrix m n α :=
  of fun i j =>
    if i = r1 then
      A.get r2 j
    else if i = r2 then
      A.get r1 j
    else
      A.get i j

/-- Scale one row of a dense matrix by a scalar. -/
def scaleRow {m n : Nat} {α : Type u} [Mul α]
    (A : DenseMatrix m n α) (r : Fin m) (c : α) : DenseMatrix m n α :=
  of fun i j =>
    if i = r then
      c * A.get i j
    else
      A.get i j

/-- Replace `tgt` by `tgt + k * src`, with the diagonal case treated as scaling. -/
def replaceRow {m n : Nat} {α : Type u} [Add α] [Mul α] [One α]
    (A : DenseMatrix m n α) (src tgt : Fin m) (k : α) : DenseMatrix m n α :=
  if src = tgt then
    scaleRow A tgt (k + 1)
  else
    of fun i j =>
      if i = tgt then
        A.get tgt j + k * A.get src j
      else
        A.get i j

theorem toMatrix_swap_eq_swap_toMatrix {m n : Nat} {α : Type u} [Semiring α]
    (A : DenseMatrix m n α) (r1 r2 : Fin m) : toMatrix (swapRow A r1 r2) = (Matrix.swap α r1 r2) * (toMatrix A) :=
    sorry

theorem toMatrix_scale_eq_scale_toMatrix {m n : Nat} {α : Type u} [CommRing α]
    (A : DenseMatrix m n α) (r : Fin m) (c : α) : toMatrix (scaleRow A r c) = (Matrix.transvection r r (c - 1)) * (toMatrix A) :=
    sorry

theorem toMatrix_replace_eq_replace_toMatrix {m n : Nat} {α : Type u} [CommRing α]
    (A : DenseMatrix m n α) (src tgt : Fin m) (k : α) : toMatrix (replaceRow A src tgt k) = (Matrix.transvection tgt src k) * (toMatrix A) :=
    sorry

end DenseMatrix
