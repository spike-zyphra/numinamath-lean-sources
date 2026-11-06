import Mathlib

theorem algebra_11140 : (1 - Complex.I) / (2 + 3 * Complex.I) = -1 / 13 - 5 / 13 * Complex.I := by 
  field_simp [Complex.ext_iff, Complex.I_mul_I]
  all_goals norm_num [Complex.I_mul_I]