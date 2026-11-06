import Mathlib

theorem number_theory_166537 : (∑ i in Finset.range 2016, ⌊(2^i / 25 : ℚ)⌋) % 100 = 14 := by
  native_decide