import Mathlib

theorem algebra_21778 (h : ℝ) (heq : h = 360 / 12) : h / 2 + 2 * h = 75 := by
  rw [heq]
  norm_num