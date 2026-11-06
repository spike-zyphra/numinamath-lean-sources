import Mathlib

theorem number_theory_192648 : (111110 / 111111 : ℚ) < (333331 / 333334 : ℚ) ∧ (333331 / 333334 : ℚ) < (222221 / 222223 : ℚ) := by
  constructor
  · norm_num
  · norm_num