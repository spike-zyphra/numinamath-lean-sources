import Mathlib

theorem algebra_17195 (a : ℝ) (ha : a ≠ 0) (h : a = 3) : 10 * a ^ 3 / (55 * a ^ 2) = 6 / 11 := by
  rw [h]
  norm_num