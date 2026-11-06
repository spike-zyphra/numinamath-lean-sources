import Mathlib

def values : ℤ × ℤ := (6, 3)

theorem algebra_1243 : values.1 ^ 2 + values.2 = 39 := by
  rw [values]
  norm_num