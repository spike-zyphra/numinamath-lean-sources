import Mathlib

/-Find the units digit of the following within the indicated number base: $52_7 + 62_7$-/
theorem number_theory_15730 : (5* 7 + 2 + 6 * 7 + 2) % 7 = 4 := by
  -- the units digit of number in base 7 is the remainder divided by 7. 
  simp
