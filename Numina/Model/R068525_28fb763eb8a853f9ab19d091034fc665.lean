import Mathlib

theorem number_theory_290912 : (Nat.digits 10 (∑ i ∈ Finset.range 2017, (10^(i + 1) - 1))).count 1 = 2013 := by 
  native_decide