import Mathlib

theorem number_theory_155364 : (∑ i ∈ Finset.range 2021, (10^(i + 1) - 1) * 7 / (10 - 1)) % 10000 = 4847 := by 
  native_decide