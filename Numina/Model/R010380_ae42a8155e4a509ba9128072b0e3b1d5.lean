import Mathlib

theorem algebra_19992 {x : ℝ} (h : x * 0.4 = 14.40) : x = 36 := by
  norm_num at h ⊢
  linarith