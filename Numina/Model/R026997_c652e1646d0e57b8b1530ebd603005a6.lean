import Mathlib

theorem number_theory_246839 : (∑ i ∈ Finset.range 2016, ⌊(7^(i+1))/(8 : ℚ)⌋) % 50 = 42 := by 
  native_decide