import Mathlib

theorem algebra_244776 (d : ℝ) (h : d = 79) (r : ℝ) (hr : r = 5) (h' : r > 0)
    (h'' : d > 0) (e : ℝ) (he : e = 1.079) (h'''' : e > 0) (r' : ℝ) (hr' : r' = 0.2)
    (h''''' : r' > 0) (h'''''' : d / r = 16 * r') :
    (60 * e) / (d / r + r' * d / (2 * r)) = 0.0812 := by
  rw [h, hr, he, hr'] at *
  norm_num at h'''''' ⊢
  all_goals linarith