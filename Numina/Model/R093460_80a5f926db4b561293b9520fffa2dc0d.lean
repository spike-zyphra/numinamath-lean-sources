import Mathlib

theorem algebra_8252 (a : ℤ) (ha : a = 3 ^ 3) : a + a + a = 3 ^ 4 := by
  rw [ha]
  norm_num