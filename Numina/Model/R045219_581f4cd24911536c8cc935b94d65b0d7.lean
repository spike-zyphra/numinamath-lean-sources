import Mathlib

theorem algebra_13816 : (2 + 2 * Complex.I) / (-3 + 4 * Complex.I) = 2 / 25 - 14 * Complex.I / 25 := by
  field_simp [Complex.ext_iff, Complex.I_mul_I]
  <;> norm_num