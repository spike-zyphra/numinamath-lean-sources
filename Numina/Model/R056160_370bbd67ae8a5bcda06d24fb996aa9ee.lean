import Mathlib

theorem algebra_14794 : (3 + 5 * .I : ℂ) / (3 - 5 * .I) + (3 - 5 * .I) / (3 + 5 * .I) = -16 / 17 := by
  field_simp [Complex.ext_iff, Complex.I_mul_I]
  norm_num