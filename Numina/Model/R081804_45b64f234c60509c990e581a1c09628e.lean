import Mathlib

theorem algebra_6136 {m b : ℝ} (h : m * 10 + b = 6) (h' : m * 18 + b = -4) :
    -b / m = 14.8 := by
  have eq1 : m = -5 / 4 := by
    linarith
  have eq2 : b = 37 / 2 := by
    rw [eq1] at h
    linarith
  rw [eq2, eq1]
  norm_num
  all_goals norm_num
  all_goals tauto