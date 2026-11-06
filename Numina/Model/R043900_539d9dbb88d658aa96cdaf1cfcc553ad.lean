import Mathlib

theorem algebra_14832 : (3 + 4 * .I : ℂ) / (1 + 2 * .I) = (11 / 5 - 2 / 5 * .I) := by 
  field_simp [Complex.ext_iff, Complex.I_mul_I]
  norm_num