import Mathlib

theorem algebra_275955 (x : ℝ) (hx : 0 < x) (h : (1 + x) * 0.612 = 1 * 0.1 + (2 / 3) * 0.3 + x * 0.612) :
    x = 0.25 := by
  norm_num at h
  all_goals linarith