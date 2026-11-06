import Mathlib

theorem number_theory_268087 :
    ∑ p in (Nat.divisors 75).filter (fun p => p > 0), p = 124 := by 
  native_decide