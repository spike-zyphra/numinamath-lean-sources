import Mathlib

theorem algebra_20610 : (-3 + 4 * Complex.I) / (1 + 2 * Complex.I) = 1 + 2 * Complex.I := by
  field_simp [Complex.ext_iff, Complex.I_mul_I]
  <;> norm_num