import Mathlib

theorem algebra_170276 (a b : ℝ) (ha : a ≠ 0) (h : a * 2 + b - 5 = 0) :
    4 * a^2 + b^2 + 4 * a * b - 2 * a - b + 3 = 23 := by
  have eq1 : 2 * a + b = 5 := by
    linarith
  have h2 : 4 * a^2 + b^2 + 4 * a * b - 2 * a - b + 3 = (2 * a + b)^2 - (2 * a + b) + 3 := by
    ring
  rw [h2]
  rw [eq1]
  norm_num