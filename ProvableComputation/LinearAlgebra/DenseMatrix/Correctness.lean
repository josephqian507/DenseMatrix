import Mathlib.LinearAlgebra.Matrix.Defs
import ProvableComputation.LinearAlgebra.DenseMatrix.Defs

/-!
# Dense matrix proofs

This file contains proofs that the DenseMatrix operations commute with
conversion to mathlib `Matrix`.
-/

universe u

namespace DenseMatrix

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

-- Reading a dense matrix built from a function-backed matrix returns the source
-- entry.
theorem get_ofMatrix {m n : Nat} {α : Type u}
    (M : Matrix (Fin m) (Fin n) α) (i : Fin m) (j : Fin n) :
    get (ofMatrix M) i j = M i j := by
  simp [ofMatrix, get, Vector.get, rowMajorIndex_div, rowMajorIndex_mod]

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

/- --- Step 1: Characterize the `dot` accumulator loop --- -/
private theorem dot_eq_sum_plus {m k n : Nat} {α : Type u} [Semiring α]
    (sum : α) (i : Fin m) (j : Fin n) (l : Fin k)
    (A : DenseMatrix m k α) (B : DenseMatrix k n α) :
    DenseMatrix.dot sum i j l A B = sum + ∑ x : Fin k, if x ≥ l then A.get i x * B.get x j else 0 := by
  -- We prove this by well-founded induction on the remaining distance `k - l.val`
  induction h_step : k - l.val generalizing l sum with
  | zero =>
    omega
  | succ =>
    rename_i n ih
    unfold DenseMatrix.dot
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
    DenseMatrix.dot 0 i j 0 A B = ∑ l : Fin k, A.get i l * B.get l j := by
  rw [dot_eq_sum_plus 0 i j 0 A B, zero_add]
  congr 1

-- TODO: fill in sorries with ai
/- --- Step 2: Characterize the flat array building loop --- -/
private theorem mul_helper_spec {m k n : Nat} {α : Type u} [Semiring α] [Inhabited α]
    [NeZero m] [NeZero k] [NeZero n]
    (out : Array α) (i j : Nat) (A : DenseMatrix m k α) (B : DenseMatrix k n α)
    (h_size : out.size = i * n + j) (hi : m ≥ i + 1) (hj : n ≥ j + 1)
    -- (h_out : ∀ (idx : Fin (m * n)), idx.val < out.size →
    --   out[idx.val]'(idx.isLt.trans_le (by simp [h_size])) =
    --   ∑ l : Fin k, (A.get ⟨idx.val / n, index_div_lt idx.isLt⟩ l * B.get l ⟨idx.val % n, index_mod_lt idx.isLt⟩))
    : (mul_helper out i j A B h_size hi hj) =
    Vector.ofFn (fun x : Fin (m * n) => ∑ l : Fin k, (A.get ⟨x.val / n, index_div_lt x.isLt⟩ l * B.get l ⟨x.val % n, index_mod_lt x.isLt⟩)) := by
  -- This is proven by induction matching the control flow of `mul_helper`
  -- induction i, j using mul_helper.induct generalizing out h_size hi hj with
  -- | base =>
  --   sorry
  -- | step =>
  --   sorry
  sorry

theorem mul_ofMatrix {m k n : Nat} {α : Type u} [Semiring α] [Inhabited α]
    [NeZero m] [NeZero k] [NeZero n] (A : Matrix (Fin m) (Fin k) α) (B : Matrix (Fin k) (Fin n) α)
    : mul (ofMatrix A) (ofMatrix B) = ofMatrix (A * B : Matrix (Fin m) (Fin n) α) := by
  rw [mul, DenseMatrix.mk.injEq]
  have h_spec := mul_helper_spec (Array.mkEmpty (m * n)) 0 0 (ofMatrix A) (ofMatrix B) (by simp)
    NeZero.one_le NeZero.one_le -- (by simp)
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


end DenseMatrix
