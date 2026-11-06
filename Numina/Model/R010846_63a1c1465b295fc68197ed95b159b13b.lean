import Mathlib

theorem algebra_17025 (x : ℝ) (hx : x > 0) (h : x + 1 + 2 * x + 3 * x + 4 * x + 5 * x - 1 = 540) :
    max (max (max (max (x + 1) (2 * x)) (3 * x)) (4 * x)) (5 * x - 1) = 179 := by
  have hx_eq : x = 36 := by
    linarith
  rw [hx_eq]
  norm_num [max_eq_left, max_eq_right]
  all_goals norm_num