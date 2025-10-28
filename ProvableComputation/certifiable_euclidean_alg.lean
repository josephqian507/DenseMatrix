import Lean
import Lean.Elab.Tactic
import Qq
import Mathlib.Algebra.GroupWithZero.Divisibility

structure EAState where
  x  : Int
  y  : Int
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

def produce_proof (a b d x y : Expr) : MetaM Expr := do -- d = ax + by => gcd | d, (d | a, d | b) => d | gcd


def gcd_tactic_main (goal : MVarId): OptionT MetaM Expr := do
  goal.withContext do
    let target ← goal.getType
    match (← whnfR <| ← instantiateMVars target).eq? with
    |  some (α, lhs, rhs) => {
        match gcd? (← whnfR lhs) with
        | some (a, b) => {
          let a ← evalNat a;
          let b ← evalNat b;
          let rhs ← evalNat rhs;
          have a : Nat := a;
          have b : Nat := b;
          let ((x, y, d), _) ← run_euclidean_alg a b
          if rhs == d then {
            return ← (produce_proof (toExpr a) (toExpr b) (toExpr d) (toExpr x) (toExpr y))
          } else {
            throwTacticEx `gcd_tactic goal (m!"gcd({a}, {b}) ≠ {rhs}")
          }
        }
        | none =>
          throwTacticEx `gcd_tactic goal
            "goal should be of the form `Nat.gcd a b = d`"
    }
    | none =>
      throwTacticEx `gcd_tactic goal
        "goal should an equality"

syntax (name := gcd_tactic) "gcd_tactic" : tactic

@[tactic gcd_tactic]
def evalMyRfl : Tactic := fun stx => do
  let goal ← getMainGoal
  gcd_tactic_main goal

#check Tactic

example : Nat.gcd 15 17 = 1 := by
  gcd_tactic





/--
This is a metaprogramming function that constructs a proof term for
`Nat.gcd a b = d` given expressions for `a`, `b`, `d`, `x`, `y`,
and proofs of:
1. `h_lin_combo`: (d : Int) = (a : Int) * x + (b : Int) * y
2. `h_d_div_a`  : d ∣ a
3. `h_d_div_b`  : d ∣ b

This function programmatically builds the same proof as seen in
the theorem `gcd_is_linear_combo_and_divisor`.
-/
def mkGcdProof (a b d x y : Expr) (h_lin_combo h_d_div_a h_d_div_b : Expr) : MetaM Expr := do

  -- Part 1: Prove d ∣ g
  -- h_d_div_g := Nat.dvd_gcd h_d_div_a h_d_div_b
  let h_d_div_g_proof ← mkAppM ``Nat.dvd_gcd #[h_d_div_a, h_d_div_b]

  -- Part 2: Prove g ∣ d
  -- h_g_div_a := Nat.gcd_dvd_left a b
  let h_g_div_a_proof ← mkAppM ``Nat.gcd_dvd_left #[a, b]
  -- h_g_div_b := Nat.gcd_dvd_right a b
  let h_g_div_b_proof ← mkAppM ``Nat.gcd_dvd_right #[a, b]

  -- h_g_div_a_int := Int.ofNat_dvd_ofNat.mpr h_g_div_a
  let h_g_div_a_int_proof ← mkAppM ``Iff.mpr #[mkConst ``Int.ofNat_dvd_ofNat, h_g_div_a_proof]
  -- h_g_div_b_int := Int.ofNat_dvd_ofNat.mpr h_g_div_b
  let h_g_div_b_int_proof ← mkAppM ``Iff.mpr #[mkConst ``Int.ofNat_dvd_ofNat, h_g_div_b_proof]

  -- h_g_div_ax := dvd_mul_of_dvd_left h_g_div_a_int x
  let h_g_div_ax_proof ← mkAppM ``dvd_mul_of_dvd_left #[h_g_div_a_int_proof, x]
  -- h_g_div_by := dvd_mul_of_dvd_left h_g_div_b_int y
  let h_g_div_by_proof ← mkAppM ``dvd_mul_of_dvd_left #[h_g_div_b_int_proof, y]

  -- h_g_div_sum := dvd_add h_g_div_ax h_g_div_by
  let h_g_div_sum_proof ← mkAppM ``dvd_add #[h_g_div_ax_proof, h_g_div_by_proof]

  -- h_lin_combo_symm := Eq.symm h_lin_combo
  let h_lin_combo_symm ← mkAppM ``Eq.symm #[h_lin_combo]

  -- h_g_div_d_int_proof := (Eq.symm h_lin_combo) ▸ h_g_div_sum_proof
  -- This is programmatically done with `Eq.cast`
  let h_g_div_d_int_proof ← mkAppM ``Eq.cast #[h_lin_combo_symm, h_g_div_sum_proof]

  -- h_g_div_d := Int.ofNat_dvd.mp h_g_div_d_int_proof
  let h_g_div_d_proof ← mkAppM ``Iff.mp #[mkConst ``Int.ofNat_dvd, h_g_div_d_int_proof]

  -- Part 3: Conclude g = d
  -- final_proof := Nat.dvd_antisymm h_g_div_d h_d_div_g
  let final_proof ← mkAppM ``Nat.dvd_antisymm #[h_g_div_d_proof, h_d_div_g_proof]

  return final_proof

-- We can also make a simple tactic to test this
open Lean.Elab.Tactic Lean.Meta

syntax (name := solve_gcd) "solve_gcd" : tactic

@[tactic solve_gcd]
def evalSolveGcd : Tactic := fun _ =>
  withMainContext do
    -- Get goal
    let goal ← getMainGoal
    let goalType ← goal.getType

    -- Goal should be `Nat.gcd a b = d`
    -- We need to find `a, b, d` from the goal `Nat.gcd a b = d`
    guard <| goalType.isAppOfArity ``Eq 3
    let some (_, lhs, d) := goalType.app3? ``Eq | throwError "goal is not an equality"
    guard <| lhs.isAppOfArity ``Nat.gcd 2
    let some (_, a, b) := lhs.app2? ``Nat.gcd | throwError "LHS is not Nat.gcd"

    -- Find `x` and `y` and the hypotheses in the local context
    let fvarCtx ← getLCtx
    let mut x : Option Expr := none
    let mut y : Option Expr := none
    let mut h_lin_combo : Option Expr := none
    let mut h_d_div_a : Option Expr := none
    let mut h_d_div_b : Option Expr := none

    for localDecl in fvarCtx do
      if localDecl.isImplementationDetail then
        continue
      let type := localDecl.type
      -- Find x and y (this is weak, assumes they are named x and y)
      if localDecl.userName == `x then
        x := some localDecl.toExpr
      if localDecl.userName == `y then
        y := some localDecl.toExpr

      -- Find `h_lin_combo : (d : Int) = (a : Int) * x + (b : Int) * y`
      -- This is hard to match exactly without more powerful tools.
      -- Let's just find the *names* of the hypotheses
      if localDecl.userName == `h_lin_combo then
        h_lin_combo := some localDecl.toExpr
      if localDecl.userName == `h_d_div_a then
        h_d_div_a := some localDecl.toExpr
      if localDecl.userName == `h_d_div_b then
        h_d_div_b := some localDecl.toExpr

    -- Get the Exprs from the Options
    let (some x, some y, some h_lin_combo, some h_d_div_a, some h_d_div_b) :=
      (x, y, h_lin_combo, h_d_div_a, h_d_div_b) |
      throwError "Could not find all variables (x, y) and hypotheses (h_lin_combo, h_d_div_a, h_d_div_b) in context"

    -- Call the proof-generating function
    let proofExpr ← mkGcdProof a b d x y h_lin_combo h_d_div_a h_d_div_b

    -- Assign this proof to the goal
    goal.assign proofExpr

    -- Close the goal
    replaceMainGoal []

-- Example theorem to test the tactic
example (a b d : Nat) (x y : Int)
    (h_lin_combo : (d : Int) = (a : Int) * x + (b : Int) * y)
    (h_d_div_a : d ∣ a)
    (h_d_div_b : d ∣ b) :
    Nat.gcd a b = d := by
  solve_gcd -- This tactic should now work
