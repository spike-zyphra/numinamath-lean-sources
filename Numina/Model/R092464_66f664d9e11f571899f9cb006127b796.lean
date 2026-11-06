import Mathlib

theorem algebra_102920 (a b : ℝ) (ha : a = 11 * 25) (hb : b = 7 * x) (h : (a + b) / (11 + 7) = 32) :
    x = 43 := by
  rw [ha, hb] at h
  norm_num at h 
  linarith