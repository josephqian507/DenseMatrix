import Mathlib.Data.Nat.GCD.Basic

def euclidean_gcd (a b : Nat) :=
    if h : b = 0
        then a
    else euclidean_gcd a (a % b)
termination_by b
decreasing_by {refine Nat.mod_lt a ?_; exact Nat.zero_lt_of_ne_zero h}
