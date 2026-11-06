import Mathlib

theorem number_theory_119561 : ∑ p in (Nat.primesBelow 20).filter (fun p => p > 10), p = 60 := by 
  native_decide