import Lean
import Lean.Elab.Tactic
import Qq
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Data.Nat.Cast.Basic

structure EAState where
  x : Int
  y : Int
  x' : Int
  y' : Int
deriving Repr

abbrev EAM := StateM EAState

def extendedEuclideanAlgorithm (a b : Nat) : EAM (Int × Int × Nat) := do
  if h : b = 0 then
    let s ← get
    -- In the base case, the correct coefficients are (x, y).
    return (s.x, s.y, a)
  else
    let q := Int.ofNat (a / b) -- Use Int for calculations to avoid subtraction issues
    let s ← get
    set { x := s.x', y := s.y', x' := s.x - q * s.x', y' := s.y - q * s.y' : EAState }
    extendedEuclideanAlgorithm b (a % b)
termination_by b
decreasing_by refine Nat.mod_lt a ?_; exact Nat.zero_lt_of_ne_zero h

def initialState : EAState := { x := 1, y := 0, x' := 0, y' := 1 }
#eval (extendedEuclideanAlgorithm 15 56).run initialState

def run_euclidean_alg (a b : Nat):= do (extendedEuclideanAlgorithm a b).run initialState

#eval run_euclidean_alg 15 17


open Lean Elab Tactic Meta
open Qq PrettyPrinter


-- custom recognizer for the gcd function.

@[inline] def gcd? (p : Expr) : Option (Expr × Expr) :=
  p.app2? ``Nat.gcd

-- -- d = ax + by => gcd | d, (d | a, d | b) => d | gcd
-- def produce_proof (a b d : Nat) (x y : Int) : MetaM Expr := do
--   -- let a := 10
--   -- let b := 7
--   -- let d := 8
--   -- let x := -2
--   -- let y := 4
--   let a_expr := toExpr a
--   let b_expr := toExpr b
--   let d_expr := toExpr d
--   let x_expr := toExpr x
--   let y_expr := toExpr y
--   let h_d_div_a := sorry -- d | a
--   let h_d_div_b := sorry -- d | b
--   let h_lin_combo : (d : Int) = (a : Int) * x + (b : Int) * y := Id.run do
--     ← Lean.Elab.Tactic.evalTactic (← `(tactic| try ring)) -- or abel

--   -- Part 1: Prove d ∣ g
--   -- h_d_div_g := Nat.dvd_gcd h_d_div_a h_d_div_b
--   let h_d_div_g_proof ← mkAppM ``Nat.dvd_gcd #[h_d_div_a, h_d_div_b]

--   -- Part 2: Prove g ∣ d
--   -- h_g_div_a := Nat.gcd_dvd_left a b
--   let h_g_div_a_proof ← mkAppM ``Nat.gcd_dvd_left #[a_expr, b_expr]
--   -- h_g_div_b := Nat.gcd_dvd_right a b
--   let h_g_div_b_proof ← mkAppM ``Nat.gcd_dvd_right #[a_expr, b_expr]

--   -- h_g_div_a_int := Int.ofNat_dvd_ofNat.mpr h_g_div_a
--   let h_g_div_a_int_proof ← mkAppM ``Iff.mpr #[mkConst ``Nat.cast_dvd_cast, h_g_div_a_proof] -- look into ↑ notation for casting
--   -- h_g_div_b_int := Int.ofNat_dvd_ofNat.mpr h_g_div_b
--   let h_g_div_b_int_proof ← mkAppM ``Iff.mpr #[mkConst ``Nat.cast_dvd_cast, h_g_div_b_proof]

--   -- h_g_div_ax := dvd_mul_of_dvd_left h_g_div_a_int x
--   let h_g_div_ax_proof ← mkAppM ``dvd_mul_of_dvd_left #[h_g_div_a_int_proof, x_expr]
--   -- h_g_div_by := dvd_mul_of_dvd_left h_g_div_b_int y
--   let h_g_div_by_proof ← mkAppM ``dvd_mul_of_dvd_left #[h_g_div_b_int_proof, y_expr]

--   -- h_g_div_sum := dvd_add h_g_div_ax h_g_div_by
--   let h_g_div_sum_proof ← mkAppM ``dvd_add #[h_g_div_ax_proof, h_g_div_by_proof]

--   -- h_lin_combo_symm := Eq.symm h_lin_combo
--   let h_lin_combo_symm ← mkAppM ``Eq.symm #[h_lin_combo]

--   -- h_g_div_d_int_proof := (Eq.symm h_lin_combo) ▸ h_g_div_sum_proof
--   let h_g_div_d_int_proof ← mkAppM ``Eq.subst #[h_lin_combo_symm, h_g_div_sum_proof]

--   -- h_g_div_d := Int.ofNat_dvd.mp h_g_div_d_int_proof
--   let h_g_div_d_proof ← mkAppM ``Iff.mp #[mkConst ``Int.ofNat_dvd, h_g_div_d_int_proof]

--   -- Part 3: Conclude g = d
--   -- final_proof := Nat.dvd_antisymm h_g_div_d h_d_div_g
--   let final_proof ← mkAppM ``Nat.dvd_antisymm #[h_g_div_d_proof, h_d_div_g_proof]

--   return final_proof

lemma int_bezout_implies_nat_gcd (a b d : Nat) (x y : Int)
    {h_d_dvd_a : d ∣ a} {h_d_dvd_b : d ∣ b} {h_bezout : d = a * x + b * y} :
    (d = Nat.gcd a b) := by
  -- We will prove equality using `Nat.dvd_antisymm`, which states
  -- that for any two natural numbers `m` and `n`, if `m ∣ n` and `n ∣ m`,
  -- then `m = n`.
  apply Nat.dvd_antisymm

  -- GOAL 1: Show `d ∣ Nat.gcd a b`
  -- This follows directly from the definition of GCD.
  -- Since `d` divides `a` and `d` divides `b`, it must also
  -- divide the *greatest* common divisor.
  exact Nat.dvd_gcd h_d_dvd_a h_d_dvd_b

  -- GOAL 2: Show `Nat.gcd a b ∣ d`
  -- This is where we use the Bézout hypothesis `h_bezout`.
  -- The hypothesis is in `Int`, so we must work with integers.

  -- We want to prove `Nat.gcd a b ∣ d`.
  rw [← Int.natCast_dvd_natCast]

  -- Our goal is now `(↑(Nat.gcd a b) : ℤ) ∣ (↑d : ℤ)`.
  -- We can rewrite the `↑d` using our Bézout hypothesis.
  -- `h_bezout` means rewrite from left-to-right (replace `↑d` with the sum).
  rw [h_bezout]

  -- Our goal is now `(↑(Nat.gcd a b) : ℤ) ∣ (↑a : ℤ) * x + (↑b : ℤ) * y`
  -- A number divides a sum if it divides both terms.
  apply Int.dvd_add

  -- GOAL 2a: Show `(↑(Nat.gcd a b) : ℤ) ∣ (↑a : ℤ) * x`
  · -- A number divides a product if it divides one of the factors.
    -- We will show it divides `↑a`.
    refine (mul_one (↑(a.gcd b))).symm ▸ ?_
    rw [Nat.cast_mul]
    apply Int.mul_dvd_mul
    -- Our goal is `(↑(Nat.gcd a b) : ℤ) ∣ (↑a : ℤ)`.
    -- We prove this by proving the `Nat` equivalent `Nat.gcd a b ∣ a`.
    -- `apply Nat.cast_dvd_cast.mp` (modus ponens) changes the `Int` goal
    -- to a `Nat` goal, as it states `m ∣ n → (↑m : ℤ) ∣ (↑n : ℤ)`.
    {
      rw [Int.natCast_dvd_natCast]
    -- This is true by the definition of `gcd`.
      apply Nat.gcd_dvd_left
    }
    { apply Int.one_dvd }

  -- GOAL 2b: Show `(↑(Nat.gcd a b) : ℤ) ∣ (↑b : ℤ) * y`
  · -- Similarly, we show it divides `↑b`.
    refine (mul_one (↑(a.gcd b))).symm ▸ ?_
    rw [Nat.cast_mul]
    apply Int.mul_dvd_mul
    -- Our goal is `(↑(Nat.gcd a b) : ℤ) ∣ (↑b : ℤ)`.
    -- Use `mp` to change the goal from `Int` to `Nat`.
    {
      rw [Int.natCast_dvd_natCast]
    -- This is true by the definition of `gcd`.
      apply Nat.gcd_dvd_right
    }
    { apply Int.one_dvd }

def gcd_tactic_main (goal : MVarId): TacticM Unit := do
  goal.withContext do
    let target ← goal.getType
    match (← whnfR <| ← instantiateMVars target).eq? with
    |  some (α, lhs, rhs) => {
        match gcd? (← whnfR lhs) with
        | some (a, b) => {
          let aNat ← match (← (evalNat a).run) with
            | some val => pure val
            | none => throwTacticEx `gcd_tactic goal "goal should be of the form `Nat.gcd a b = d`"
          let bNat ← match (← (evalNat b).run) with
            | some val => pure val
            | none => throwTacticEx `gcd_tactic goal "goal should be of the form `Nat.gcd a b = d`"
          let rhs ← match (← (evalNat rhs).run) with
            | some val => pure val
            | none => throwTacticEx `gcd_tactic goal "goal should be of the form `Nat.gcd a b = d`"
          have aNat : Nat := aNat;
          have bNat : Nat := bNat;
          let ((x, y, d), _) ← run_euclidean_alg aNat bNat
          if rhs == d then {
            let lemmaWithArgs ← mkAppM ``int_bezout_implies_nat_gcd
              #[a, b, toExpr d, toExpr x, toExpr y]
            let newGoals ← goal.apply lemmaWithArgs

            let mut unsolvedGoals : List MVarId := [];
            for goal in newGoals do
              let goalType ← goal.getType
              if (!goalType.isAppOf ``Dvd) then -- wtf
                try
                  let decideAction := runTactic goal (← `(tactic| decide))
                  let (_, _) ← decideAction
                catch e =>
                  logError m!"'decide' tactic failed on divisibility goal: {e.toMessageData}"
                  unsolvedGoals := goal :: unsolvedGoals
              else
                try
                  let abelAction := runTactic goal (← `(tactic| abel))
                  let (_, _) ← abelAction
                catch e =>
                  logError m!"'abel' tactic failed on Bezout goal: {e.toMessageData}"
                  unsolvedGoals := goal :: unsolvedGoals

            --let replaceAction := runTactic goal (replaceMainGoal unsolvedGoals.reverse)

            logInfo m!"'gcd_tactic' finished. {3 - unsolvedGoals.length}/3 subgoals solved."
          } else {
            throwTacticEx `gcd_tactic goal (
              m!"Tactic failed: computed GCD {d} does not match goal {rhs}"
            )
          }
        }
        | none =>
          throwTacticEx `gcd_tactic goal
            "goal should be of the form `Nat.gcd a b = d`"
    }
    | none =>
      throwTacticEx `gcd_tactic goal
        "goal should be an equality"

syntax (name := gcd_tactic) "gcd_tactic" : tactic

@[tactic gcd_tactic]
def evalMyRfl : Tactic := fun stx => do
  let goal ← getMainGoal
  gcd_tactic_main goal

example : Nat.gcd 15 17 = 1 := by
  gcd_tactic
