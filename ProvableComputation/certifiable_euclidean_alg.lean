import Lean
import Lean.Elab.Tactic
import Qq

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

def gcd_tactic_main (goal : MVarId): OptionT MetaM Unit := do
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
            produce_proof
          }
          else return Unit.unit--throwTacticEx {sorry} {sorry} "sorry"
        }
        | none => return Unit.unit--throwTacticEx {sorry} {sorry} "sorry"
    }
    |  none => return Unit.unit --throwTacticEx {sorry} {sorry} "sorry"



syntax (name := gcd_tactic) "gcd_tactic" : tactic

@[tactic gcd_tactic]
def evalMyRfl : Tactic := fun stx => do
  let goal ← getMainGoal
  gcd_tactic_main goal

#check Tactic

example : Nat.gcd 15 17 = 1 := by
  gcd_tactic
