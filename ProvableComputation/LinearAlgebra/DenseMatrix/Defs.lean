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

namespace RowMajorIndex

/--
When a proof starts from typed indices `i : Fin m` and `j : Fin n`, the
witness `j` proves `n > 0`: `0 <= j.val < n`. That positivity is what lets
the division and modulo simplification lemmas recover `i.val` and `j.val`
from the flattened row-major offset.

Dividing a flattened typed row-major index by the row width recovers the
row.
-/
theorem div_eq_row {m n : Nat} (i : Fin m) (j : Fin n) :
    rowMajorIndex i j / n = i.val := by
  unfold rowMajorIndex
  rw [Nat.mul_comm i.val n]
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  rw [Nat.mul_add_div hn, Nat.div_eq_of_lt j.isLt, Nat.add_zero]

/-- Taking a flattened typed row-major index modulo the row width recovers the column. -/
theorem mod_eq_col {m n : Nat} (i : Fin m) (j : Fin n) :
    rowMajorIndex i j % n = j.val := by
  unfold rowMajorIndex
  rw [Nat.mul_comm i.val n]
  rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt j.isLt]

/-- Two typed row-major indices are equal exactly when both coordinates are equal. -/
theorem eq_iff {m n : Nat} {i₁ i₂ : Fin m} {j₁ j₂ : Fin n} :
    rowMajorIndex i₁ j₁ = rowMajorIndex i₂ j₂ ↔ i₁ = i₂ ∧ j₁ = j₂ := by
  constructor
  · intro h
    constructor
    · apply Fin.ext
      rw [← div_eq_row i₁ j₁, h, div_eq_row i₂ j₂]
    · apply Fin.ext
      rw [← mod_eq_col i₁ j₁, h, mod_eq_col i₂ j₂]
  · rintro ⟨rfl, rfl⟩
    rfl

end RowMajorIndex

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
  simp [ofMatrix, get, Vector.get, RowMajorIndex.div_eq_row, RowMajorIndex.mod_eq_col]

theorem get_toMatrix {m n : Nat} {α : Type u} (A : DenseMatrix m n α) (i : Fin m) (j : Fin n)
    : (toMatrix A) i j = get A i j := by
  rfl

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

/-- Two DenseMatrices are equal iff their underlying Vectors are equal at every single index. -/
@[ext]
theorem ext {m n : Nat} {α : Type u} : ∀ {M N : DenseMatrix m n α}
    (_ : ∀ i : Fin m, ∀ j : Fin n, DenseMatrix.get M i j = DenseMatrix.get N i j), M = N
  | ⟨M_data⟩, ⟨N_data⟩, h => by
    rw [DenseMatrix.mk.injEq]
    apply Vector.ext
    intro x hx
    let idx : Fin (m * n) := ⟨x, hx⟩
    change M_data.get idx = N_data.get idx
    rw [←get_unflatten, ←get_unflatten]
    exact h ⟨x / n, index_div_lt hx⟩ ⟨x % n, index_mod_lt hx⟩

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

@[simp]
theorem of_apply {m n : Nat} {α : Type u} (f : Fin m → Fin n → α) (i j)
    : (of f).get i j = f i j := by
  exact get_ofMatrix (Matrix.of f) i j

/-- Constructs an m by n zero matrix. -/
def zero {m n : Nat} {α : Type u} [Zero α] : DenseMatrix m n α :=
  of fun _ _ => 0

/-- Registers the `0` literal for DenseMatrix. -/
instance {m n : Nat} {α : Type u} [Zero α] : Zero (DenseMatrix m n α) where
  zero := zero

theorem zero_ofMatrix {m n : Nat} {α : Type u} [Zero α] :
    ofMatrix (0 : Matrix (Fin m) (Fin n) α) = 0 := by
  ext i j
  change (ofMatrix 0).get i j = zero.get i j
  rw [zero, get_ofMatrix, of_apply]
  rfl

theorem zero_toMatrix {m n : Nat} {α : Type u} [Zero α] :
    toMatrix (0 : DenseMatrix m n α) = 0 := by
  ext i j
  change (toMatrix zero) i j = (0 : Matrix (Fin m) (Fin n) α) i j
  rw [zero, get_toMatrix, of_apply]
  rfl

/-- Constructs an n by n identity matrix. -/
def identity {n : Nat} {α : Type u} [Zero α] [One α] :
    DenseMatrix n n α :=
  of fun i j => if i = j then 1 else 0

/-- Registers the `1` literal for square DenseMatrices. -/
instance {n : Nat} {α : Type u} [Zero α] [One α] : One (DenseMatrix n n α) where
  one := identity

theorem one_ofMatrix {n : Nat} {α : Type u} [Zero α] [One α] :
    ofMatrix (1 : Matrix (Fin n) (Fin n) α) = 1 := by
  ext i j
  change (ofMatrix 1).get i j = identity.get i j
  rw [identity, get_ofMatrix, of_apply]
  rfl

theorem one_toMatrix {n : Nat} {α : Type u} [Zero α] [One α] :
    toMatrix (1 : DenseMatrix n n α) = 1 := by
  ext i j
  change (toMatrix identity) i j = (1 : Matrix (Fin n) (Fin n) α) i j
  rw [identity, get_toMatrix, of_apply]
  rfl

def neg {m n : Nat} {α : Type u} [Neg α] :
    DenseMatrix m n α → DenseMatrix m n α :=
  fun A => of (fun i j => -A.get i j)

instance {m n : Nat} {α : Type u} [Neg α] : Neg (DenseMatrix m n α) where
  neg := neg

theorem neg_ofMatrix {m n : Nat} {α : Type u} [Neg α] (M : Matrix (Fin m) (Fin n) α) :
    ofMatrix (-M) = -(ofMatrix M) := by
  ext i j
  change (ofMatrix (-M)).get i j = (of (fun k l => -(ofMatrix M).get k l)).get i j
  rw [get_ofMatrix, of_apply, get_ofMatrix]
  rfl

theorem neg_toMatrix {m n : Nat} {α : Type u} [Neg α] (M : DenseMatrix m n α) :
    toMatrix (-M) = -(toMatrix M) := by
  ext i j
  change (toMatrix (of (fun k l => -M.get k l))) i j = -(toMatrix M) i j
  rw [get_toMatrix, of_apply, get_toMatrix]

def add {m n : Nat} {α : Type u} [Add α] (A B : DenseMatrix m n α) : DenseMatrix m n α where
  data := A.data.zipWith (· + ·) B.data

instance {m n : Nat} {α : Type u} [Add α] : Add (DenseMatrix m n α) := ⟨add⟩

theorem add_ofMatrix {m n : Nat} {α : Type u} [Add α] (A B : Matrix (Fin m) (Fin n) α)
    : (ofMatrix A) + (ofMatrix B) = ofMatrix (A + B) := by
  change add (ofMatrix A) (ofMatrix B) = ofMatrix (A + B)
  rw [add, DenseMatrix.mk.injEq]
  apply Vector.ext
  intro x hx
  simp [ofMatrix]

theorem add_toMatrix {m n : Nat} {α : Type u} [Add α] (A B : DenseMatrix m n α)
    : toMatrix (A + B) = (toMatrix A) + (toMatrix B) := by
  change toMatrix (add A B) = (toMatrix A) + (toMatrix B)
  let M := toMatrix A
  let N := toMatrix B
  suffices ofMatrix (toMatrix (add (ofMatrix M) (ofMatrix N)))
    = ofMatrix ((toMatrix (ofMatrix M)) + (toMatrix (ofMatrix N))) from by aesop
  rw [ofMatrix_toMatrix, toMatrix_ofMatrix, toMatrix_ofMatrix]
  exact add_ofMatrix M N

-- Benchmarked by `lake exe densematrix_bench --profile smoke --jsonl` against mathlib Matrix.smul.
def smul {m n : Nat} {α : Type u} [Mul α] (c : α) (M : DenseMatrix m n α) : DenseMatrix m n α where
  data := M.data.map (fun x => c * x)

-- Benchmarked by `lake exe densematrix_bench --profile smoke --jsonl` against `sum_dot`.
/--
Given indices `i` and `j`, returns the dot product of the i-th row of `A` and the j-th column
of `B `.

dotProduct is used to simplify the recursive function used for mul.

Note: dot products are defined for function-backed vector representation in Mathlib.Data.Matrix.Mul.
-/
private def dotProduct_helper {m k n : Nat} {α : Type u} [Zero α] [Add α] [Mul α]
    (sum : α) (i : Fin m) (j : Fin n) (l : Fin k)
    (M : DenseMatrix m k α) (N : DenseMatrix k n α) : α :=
  if h: l + 1 < k then
    dotProduct_helper (sum + (M.get i l * N.get l j)) i j ⟨l+1, by simp [h]⟩ M N
  else
    sum + (M.get i l * N.get l j)

def dotProduct {m k n : Nat} {α : Type u} [Zero α] [Add α] [Mul α] [NeZero k]
    (i : Fin m) (j : Fin n) (M : DenseMatrix m k α) (N : DenseMatrix k n α) : α :=
  dotProduct_helper 0 i j ⟨0, Nat.pos_of_neZero k⟩ M N

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
  let entry := dotProduct ⟨i, by exact Nat.lt_of_succ_le hi⟩ ⟨j, by exact Nat.lt_of_succ_le hj⟩ A B
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
  : HMul (DenseMatrix m k α) (DenseMatrix k n α) (DenseMatrix m n α) where
  hMul A B := mul A B

/- --- Step 1: Characterize the `dot` accumulator loop --- -/
private theorem dot_eq_sum_plus {m k n : Nat} {α : Type u} [Semiring α]
    (sum : α) (i : Fin m) (j : Fin n) (l : Fin k)
    (A : DenseMatrix m k α) (B : DenseMatrix k n α) :
    dotProduct_helper sum i j l A B = sum + ∑ x : Fin k, if x ≥ l then A.get i x * B.get x j else 0 := by
  -- We prove this by well-founded induction on the remaining distance `k - l.val`
  induction h_step : k - l.val generalizing l sum with
  | zero =>
    omega
  | succ =>
    rename_i n ih
    unfold dotProduct_helper
    have h_next : k - (l.val + 1) = n := by omega
    split_ifs with h₁
    · rw [ih (sum + A.get i l * B.get l j) ⟨l + 1, h₁⟩ h_next]
      rw [add_assoc]
      congr 1
      have h_split : (∑ x : Fin k, if x ≥ l then A.get i x * B.get x j else 0) =
          (if l ≥ l then A.get i l * B.get l j else 0) +
          (∑ x : Fin k, if x ≥ ⟨l.val + 1, h₁⟩ then A.get i x * B.get x j else 0) := by
        -- 1. Extract `l` from the LHS sum
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
        -- 2. Extract `l` from the RHS sum
        have h_rhs_split : (∑ x : Fin k, if x ≥ ⟨l.val + 1, h₁⟩ then A.get i x * B.get x j else 0) =
            (if l ≥ ⟨l.val + 1, h₁⟩ then A.get i l * B.get l j else 0) +
            ∑ x ∈ Finset.univ.erase l, if x ≥ ⟨l.val + 1, h₁⟩ then A.get i x * B.get x j else 0 :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ l)).symm
        rw [h_rhs_split]
        have hl_false : ¬ ((l : Fin k) ≥ ⟨l.val + 1, h₁⟩) := by
          intro h
          have : l.val ≥ l.val + 1 := h
          omega
        simp only [hl_false, ite_false, zero_add]
        congr 1
        apply Finset.sum_congr rfl
        intro x hx
        have h_ne : x.val ≠ l.val := by
          intro h_eq
          have : x = l := Fin.ext h_eq
          exact (Finset.mem_erase.mp hx).1 this
        have h_iff : x ≥ l ↔ x ≥ ⟨l.val + 1, h₁⟩ := by
          constructor
          · intro h
            have h_le : l.val ≤ x.val := h
            have h_lt : l.val < x.val := Nat.lt_of_le_of_ne h_le h_ne.symm
            exact h_lt
          · intro h
            have : x.val ≥ l.val + 1 := h
            omega
        simp only [h_iff]
      rw [h_split]
      simp only [ge_iff_le, le_refl, ite_true]
    · push Not at h₁
      have h_eq : k = l.val + 1 := le_antisymm h₁ (by omega)
      congr 1
      symm
      rw [Finset.sum_eq_single l]
      · simp only [ge_iff_le, le_refl, ite_true]
      · intro x _ hx_ne
        have h_not_ge : ¬(x ≥ l) := by
          intro h_ge
          have h_le : l.val ≤ x.val := h_ge
          have h_lt : x.val < l.val + 1 := by
            rw [← h_eq]
            exact x.isLt
          have h_le_rev : x.val ≤ l.val := Order.le_of_lt_add_one h_lt
          have h_val_eq : x.val = l.val := le_antisymm h_le_rev h_le
          exact hx_ne (Fin.ext h_val_eq)
        simp only [h_not_ge, ite_false]
      · intro h_abs
        exact False.elim (h_abs (Finset.mem_univ l))

/-- Core specification lemma for `dot` starting at 0 -/
private theorem dot_zero_eq_matrix_mul {m k n : Nat} {α : Type u} [Semiring α] [NeZero k]
    (i : Fin m) (j : Fin n) (A : DenseMatrix m k α) (B : DenseMatrix k n α) :
    dotProduct i j A B = ∑ l : Fin k, A.get i l * B.get l j := by
  unfold dotProduct
  rw [dot_eq_sum_plus 0 i j ⟨0, _⟩ A B, zero_add]
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
  have h_entry : dotProduct ⟨i, Nat.lt_of_succ_le hi⟩ ⟨j, Nat.lt_of_succ_le hj⟩ A B =
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
      have h_div : out.size / n = i := by rw [h_out', RowMajorIndex.div_eq_row]
      have h_mod : out.size % n = j := by rw [h_out', RowMajorIndex.mod_eq_col]
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
        have h_div : out.size / n = i := by rw [h_out', RowMajorIndex.div_eq_row]
        have h_mod : out.size % n = j := by rw [h_out', RowMajorIndex.mod_eq_col]
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
        have h_div : x / n = i := by rw [h_eq_size, h_out', RowMajorIndex.div_eq_row]
        have h_mod : x % n = j := by rw [h_eq_size, h_out', RowMajorIndex.mod_eq_col]
        simp [←h_eq_size, h_div, h_mod]

theorem mul_ofMatrix {m k n : Nat} {α : Type u} [Semiring α] [Inhabited α]
    [NeZero m] [NeZero k] [NeZero n] (A : Matrix (Fin m) (Fin k) α) (B : Matrix (Fin k) (Fin n) α) :
    -- mul (ofMatrix A) (ofMatrix B) = ofMatrix (A * B : Matrix (Fin m) (Fin n) α) := by
    (ofMatrix A) * (ofMatrix B) = ofMatrix (A * B : Matrix (Fin m) (Fin n) α) := by
  change mul (ofMatrix A) (ofMatrix B) = ofMatrix (A * B : Matrix (Fin m) (Fin n) α)
  rw [mul, DenseMatrix.mk.injEq]
  have h_spec := mul_helper_spec (Array.mkEmpty (m * n)) 0 0 (ofMatrix A) (ofMatrix B) (by simp)
    NeZero.one_le NeZero.one_le (by simp)
  apply Vector.ext
  intro i x
  rw [h_spec]
  nth_rewrite 3 [ofMatrix]
  simp only [Vector.getElem_ofFn, Matrix.mul_apply, get_ofMatrix]

theorem mul_toMatrix {m k n : Nat} {α : Type u} [Semiring α] [Inhabited α]
    [NeZero m] [NeZero k] [NeZero n] (A : DenseMatrix m k α) (B : DenseMatrix k n α) :
    toMatrix (A * B) = (toMatrix A) * (toMatrix B) := by
  change toMatrix (mul A B) = (toMatrix A) * (toMatrix B)
  let M := toMatrix A
  let N := toMatrix B
  suffices ofMatrix (toMatrix (mul (ofMatrix M) (ofMatrix N)))
    = ofMatrix ((toMatrix (ofMatrix M)) * (toMatrix (ofMatrix N))) from by aesop
  rw [ofMatrix_toMatrix, toMatrix_ofMatrix, toMatrix_ofMatrix]
  exact mul_ofMatrix M N

instance {n : Nat} {α : Type u} [Semiring α] [Inhabited α] [NeZero n] :
    Semiring (DenseMatrix n n α) where
  -- 1. Map to your existing high-performance operations
  add := (· + ·)
  mul := (· * ·)
  zero := 0
  one := 1
  nsmul := nsmulRec

  -- 2. Provide the proofs for the axioms (placeholders for now)
  add_assoc := fun A B C => by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    simp only [add_toMatrix]
    exact add_assoc (toMatrix A) (toMatrix B) (toMatrix C)
  zero_add := fun A => by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    simp only [add_toMatrix, zero_toMatrix]
    exact zero_add (toMatrix A)
  add_zero := fun A => by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    simp only [add_toMatrix, zero_toMatrix]
    exact add_zero (toMatrix A)
  add_comm := fun A B => by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    simp only [add_toMatrix]
    apply add_comm (toMatrix A) (toMatrix B)
  mul_assoc := fun A B C => by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    simp only [mul_toMatrix]
    exact mul_assoc (toMatrix A) (toMatrix B) (toMatrix C)
  zero_mul := fun A => by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    simp only [mul_toMatrix, zero_toMatrix]
    exact zero_mul (toMatrix A)
  mul_zero := fun A => by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    simp only [mul_toMatrix, zero_toMatrix]
    exact mul_zero (toMatrix A)
  one_mul := fun A => by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    simp only [mul_toMatrix, one_toMatrix]
    exact one_mul (toMatrix A)
  mul_one := fun A => by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    rw [mul_toMatrix, one_toMatrix]
    exact mul_one (toMatrix A)
  left_distrib := fun A B C => by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    rw [mul_toMatrix, add_toMatrix, add_toMatrix, mul_toMatrix, mul_toMatrix]
    exact mul_add (toMatrix A) (toMatrix B) (toMatrix C)
  right_distrib := fun A B C => by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    rw [mul_toMatrix, add_toMatrix, add_toMatrix, mul_toMatrix, mul_toMatrix]
    exact add_mul (toMatrix A) (toMatrix B) (toMatrix C)

instance {n : Nat} {α : Type u} [Ring α] [Inhabited α] [NeZero n] :
    Ring (DenseMatrix n n α) where
  -- 1. Map to your existing high-performance operations
  add := (· + ·)
  mul := (· * ·)
  zero := 0
  one := 1
  neg := fun A => -A
  nsmul := nsmulRec
  zsmul := zsmulRec

  -- 2. Provide the proofs for the axioms (placeholders for now)
  add_assoc := fun A B C => by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    simp only [add_toMatrix]
    exact add_assoc (toMatrix A) (toMatrix B) (toMatrix C)
  zero_add := fun A => by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    simp only [add_toMatrix, zero_toMatrix]
    exact zero_add (toMatrix A)
  add_zero := fun A => by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    simp only [add_toMatrix, zero_toMatrix]
    exact add_zero (toMatrix A)
  add_comm := fun A B => by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    simp only [add_toMatrix]
    apply add_comm (toMatrix A) (toMatrix B)
  neg_add_cancel := fun A => by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    simp only [add_toMatrix, zero_toMatrix, neg_toMatrix]
    apply neg_add_cancel
  mul_assoc := fun A B C => by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    simp only [mul_toMatrix]
    exact mul_assoc (toMatrix A) (toMatrix B) (toMatrix C)
  zero_mul := fun A => by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    simp only [mul_toMatrix, zero_toMatrix]
    exact zero_mul (toMatrix A)
  mul_zero := fun A => by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    simp only [mul_toMatrix, zero_toMatrix]
    exact mul_zero (toMatrix A)
  one_mul := fun A => by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    simp only [mul_toMatrix, one_toMatrix]
    exact one_mul (toMatrix A)
  mul_one := fun A => by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    rw [mul_toMatrix, one_toMatrix]
    exact mul_one (toMatrix A)
  left_distrib := fun A B C => by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    rw [mul_toMatrix, add_toMatrix, add_toMatrix, mul_toMatrix, mul_toMatrix]
    exact mul_add (toMatrix A) (toMatrix B) (toMatrix C)
  right_distrib := fun A B C => by
    apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
    rw [mul_toMatrix, add_toMatrix, add_toMatrix, mul_toMatrix, mul_toMatrix]
    exact add_mul (toMatrix A) (toMatrix B) (toMatrix C)

protected theorem mul_apply {m n k : Nat} {α : Type u} [Semiring α] [Inhabited α]
    [NeZero m] [NeZero n] [NeZero k]
    (M : DenseMatrix m k α) (N : DenseMatrix k n α) (i : Fin m) (j : Fin n) :
    (M * N).get i j = dotProduct i j M N := by
  have h_mul : (M * N).get i j = ∑ l : Fin k, M.get i l * N.get l j := by
    have h := mul_toMatrix M N
    exact congr_fun (congr_fun h i) j
  rw [h_mul]
  exact (dot_zero_eq_matrix_mul i j M N).symm

protected theorem mul_zero {m n k : Nat} {α : Type u} [Semiring α] [Inhabited α]
    [NeZero m] [NeZero n] [NeZero k]
    (M : DenseMatrix m k α) :
    M * (0 : DenseMatrix k n α) = 0 := by
  apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
  simp only [mul_toMatrix, zero_toMatrix]
  exact Matrix.mul_zero (toMatrix M)

protected theorem zero_mul {m n k : Nat} {α : Type u} [Semiring α] [Inhabited α]
    [NeZero m] [NeZero n] [NeZero k]
    (M : DenseMatrix k n α) :
    (0 : DenseMatrix m k α) * M = 0 := by
  apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
  simp only [mul_toMatrix, zero_toMatrix]
  exact Matrix.zero_mul (toMatrix M)

protected theorem mul_add {m n k : Nat} {α : Type u} [Semiring α] [Inhabited α]
    [NeZero m] [NeZero n] [NeZero k]
    (L : DenseMatrix m k α) (M N : DenseMatrix k n α) :
    L * (M + N) = L * M + L * N := by
  apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
  simp only [add_toMatrix, mul_toMatrix]
  exact Matrix.mul_add (toMatrix L) (toMatrix M) (toMatrix N)

protected theorem add_mul {m n k : Nat} {α : Type u} [Semiring α] [Inhabited α]
    [NeZero m] [NeZero n] [NeZero k]
    (L M : DenseMatrix m k α) (N : DenseMatrix k n α) :
    (L + M) * N = L * N + M * N := by
  apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
  simp only [add_toMatrix, mul_toMatrix]
  exact Matrix.add_mul (toMatrix L) (toMatrix M) (toMatrix N)

protected theorem mul_one {m n : Nat} {α : Type u} [Semiring α] [Inhabited α]
    [NeZero m] [NeZero n]
    (M : DenseMatrix m n α) :
    M * (1 : DenseMatrix n n α) = M := by
  apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
  simp only [mul_toMatrix, one_toMatrix]
  exact Matrix.mul_one (toMatrix M)

protected theorem one_mul {m n : Nat} {α : Type u} [Semiring α] [Inhabited α]
    [NeZero m] [NeZero n]
    (M : DenseMatrix m n α) :
    (1 : DenseMatrix m m α) * M = M := by
  apply_fun toMatrix using (fun X Y h => by rw [← ofMatrix_toMatrix X, h, ofMatrix_toMatrix Y])
  simp only [mul_toMatrix, one_toMatrix]
  exact Matrix.one_mul (toMatrix M)

protected theorem mul_assoc {l m n o : Nat} {α : Type u} [Semiring α] [Inhabited α]
    [NeZero l] [NeZero m] [NeZero n] [NeZero o]
    (L : DenseMatrix l m α) (M : DenseMatrix m n α) (N : DenseMatrix n o α) :
    L * M * N = L * (M * N) := by
  apply_fun toMatrix using (fun A B h => by rw [← ofMatrix_toMatrix A, h, ofMatrix_toMatrix B])
  rw [mul_toMatrix, mul_toMatrix, mul_toMatrix, mul_toMatrix]
  exact Matrix.mul_assoc (toMatrix L) (toMatrix M) (toMatrix N)

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
Flat transpose entries decode an output slot as a source column and row. The
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
      RowMajorIndex.div_eq_row (m := n) (n := m) ⟨j, hj_lt⟩ ⟨i, hi_lt⟩
  have hmod : out.size % m = i := by
    rw [h_size]
    simpa [rowMajorIndex] using
      RowMajorIndex.mod_eq_col (m := n) (n := m) ⟨j, hj_lt⟩ ⟨i, hi_lt⟩
  simp [transposeFlatEntry, hdiv, hmod, get_toMatrix]

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
    simpa [x] using RowMajorIndex.div_eq_row (m := n) (n := m) i j
  have hmod : x.val % m = j.val := by
    simpa [x] using RowMajorIndex.mod_eq_col (m := n) (n := m) i j
  simpa [transpose, get, x, transposeFlatEntry, hdiv, hmod, get_toMatrix] using h_get

theorem transpose_ofMatrix {m n : Nat} {α : Type u} [NeZero m] [NeZero n]
    (M : Matrix (Fin m) (Fin n) α) :
    ofMatrix M.transpose = transpose (ofMatrix M) := by
  ext i j
  simp [get_ofMatrix]

theorem transpose_toMatrix {m n : Nat} {α : Type u} [NeZero m] [NeZero n]
    (M : DenseMatrix m n α) :
    toMatrix (transpose M) = M.toMatrix.transpose := by
  ext i j
  simp [get_toMatrix]

end DenseMatrix
