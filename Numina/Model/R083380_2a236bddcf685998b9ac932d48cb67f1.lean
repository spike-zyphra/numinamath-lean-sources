import Mathlib

theorem algebra_272359 (x : ℝ) (hx : x ≠ -2 * x) (h : x = 2021) : 4 * x / (x + 2 * x) = 4 / 3 := by
  rw [h]
  norm_num