import Mathlib

theorem algebra_6313 (d : ℝ) (h : d > 0) (v : ℝ) (h' : v = 3 + 1) (h'' : d / v = 4)
    (h''' : d / (v - 1) = 6) : d = 72 := by
  have hv : v = 4 := by linarith
  rw [hv] at h'' h'''
  norm_num at h'' h'''
  all_goals linarith