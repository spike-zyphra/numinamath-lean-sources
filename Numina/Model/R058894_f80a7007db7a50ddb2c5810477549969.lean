import Mathlib

theorem algebra_235795 (x : ℝ) (h : (x - 12.12) / (1 / 5) + 1.85 = 68.5 * 0.1) :
    x = 13.12 := by
  norm_num at h 
  linarith