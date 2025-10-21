import Lean

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
