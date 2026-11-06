import Mathlib

theorem number_theory_154770 : (Nat.factorial 1 * ∏ i ∈ Finset.Icc 2 100, Nat.factorial i) % 10^1124 = 0 := by 
  native_decide