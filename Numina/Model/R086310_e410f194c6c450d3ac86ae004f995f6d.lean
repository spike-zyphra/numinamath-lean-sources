import Mathlib

theorem algebra_18790 (a : ℤ) (ha : a = 5) : a^3 * a^2 = 3125 := by
  rw [ha]
  norm_num