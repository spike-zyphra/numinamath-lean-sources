import Mathlib

theorem algebra_12691 : (4 - 5 * .I : ℂ) * (-5 + 5 * .I) = 5 + 45 * .I := by
  simp [Complex.ext_iff, Complex.I_mul_I]
  all_goals norm_num