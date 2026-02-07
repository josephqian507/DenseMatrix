import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic

import ProvableComputation.linear_algebra.EchelonCommonProofs

open Matrix
open scoped Matrix

set_option linter.style.nativeDecide false in
local macro "by_native_decide" : tactic => `(tactic| native_decide)

/-! ### Basic Pivot/Zero-Row Facts -/

def Mpivot : Matrix (Fin 2) (Fin 3) ℚ :=
  !![0, 5, 0;
    0, 0, 1]

example : IsPivot Mpivot 0 (1 : Fin 3) := by
  refine ⟨by decide, ?_⟩
  intro j hj
  fin_cases j
  · simp [Mpivot]
  · exact (False.elim (lt_irrefl _ hj))
  · exact (False.elim (Nat.not_lt_of_ge (by decide) hj))

example (p q : Fin 3) (hp : IsPivot Mpivot 0 p) (hq : IsPivot Mpivot 0 q) : p = q :=
  IsPivot.eq_of_left hp hq

def Mzero : Matrix (Fin 2) (Fin 2) ℚ :=
  !![0, 0;
    0, 0]

example : RowIsZero Mzero 0 := by
  intro j
  fin_cases j <;> simp [Mzero]

example : ¬ IsPivot Mzero 0 (0 : Fin 2) := by
  intro hp
  exact RowIsZero.not_isPivot (M := Mzero) (i := 0) (p := 0)
    (by intro j; fin_cases j <;> simp [Mzero]) hp

/-! ### `checkPivot` Examples -/

def Mscan : Matrix (Fin 2) (Fin 3) ℚ :=
  !![0, 1, 2;
    0, 0, 3]

example : checkPivot Mscan 0 0 = some ((0 : Fin 2), (1 : Fin 3)) := by
  by_native_decide

example :
    let pr : Fin 2 := 0
    let pc : Fin 3 := 1
    checkPivot Mscan 0 0 = some (pr, pc) → 0 ≤ pr.1 := by
  intro pr pc h
  exact checkPivot_some_row_ge (M := Mscan) (row := 0) (col := 0) (pr := pr) (pc := pc) h

example :
    ∀ r : Fin 2, 0 ≤ r.1 → Mscan r (0 : Fin 3) = 0 := by
  intro r hr
  have hcp : checkPivot Mscan 0 0 = some ((0 : Fin 2), (1 : Fin 3)) := by
    by_native_decide
  have hmin := checkPivot_some_minimal
    (M := Mscan) (row := 0) (col := 0) (pr := (0 : Fin 2)) (pc := (1 : Fin 3)) hcp
  have hcol : 0 ≤ (0 : Fin 3).1 := by decide
  have hj : (0 : Fin 3) < (1 : Fin 3) := by decide
  exact hmin (0 : Fin 3) hcol hj r hr

example :
    let pr : Fin 2 := 0
    let pc : Fin 3 := 1
    checkPivot Mscan 0 0 = some (pr, pc) → Mscan pr pc ≠ 0 := by
  intro pr pc h
  exact checkPivot_some_nonzero (M := Mscan) (row := 0) (col := 0) (pr := pr) (pc := pc) h

/-! ### `eliminateCol` Examples -/

def Melim : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, 2;
    3, 4]

example (j : Fin 2) :
    (eliminateCol Melim 0 0) 0 j = Melim 0 j := by
  simpa using
    eliminateCol_pivotRow
      (M := Melim)
      (pivotRow := (0 : Fin 2))
      (pivotCol := (0 : Fin 2))
      j

example : (eliminateCol Melim 0 0) 1 0 = 0 := by
  have h1 : Melim (0 : Fin 2) (0 : Fin 2) = 1 := by
    simp [Melim]
  have hz := eliminateCol_pivotCol_zero
    (M := Melim) (pivotRow := (0 : Fin 2)) (pivotCol := (0 : Fin 2)) h1
  exact hz (1 : Fin 2) (by decide)
