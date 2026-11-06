import Mathlib

theorem number_theory_259234 : ∃ n, n > 0 ∧ (n * (n + 1) * (n + 2) * (n + 3)) = 1680 := by 
  use 5
  constructor
  · norm_num -- shows 5 > 0 is true
  · norm_num -- shows 5 * 6 * 7 * 8 = 1680 is true