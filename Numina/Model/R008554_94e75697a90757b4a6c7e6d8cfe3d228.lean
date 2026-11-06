import Mathlib

theorem algebra_10308 : (5 + 12 * Complex.I) / (2 - 3 * Complex.I) = -2 + 3 * Complex.I := by
  field_simp [Complex.ext_iff, Complex.I_mul_I]
  norm_num