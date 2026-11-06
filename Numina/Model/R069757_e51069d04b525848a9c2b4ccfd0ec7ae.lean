import Mathlib

theorem algebra_8211 : Real.sqrt (1 + 2009 ^ 2 + 2009 ^ 2 / 2010 ^ 2) - 1 / 2010 = 2009 := by
  have h1 : Real.sqrt (1 + 2009 ^ 2 + 2009 ^ 2 / 2010 ^ 2) = (2009 * 2010 + 1) / 2010 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h1]
  field_simp
  <;> norm_num