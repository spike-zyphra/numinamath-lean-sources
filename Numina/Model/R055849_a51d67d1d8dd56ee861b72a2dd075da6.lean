import Mathlib

theorem algebra_95 (a b : ℝ) (ha : a = 1 / 8) (hb : b = 1 / 16)
    (h : 3 * a + 1 * b = 20) :
    1 / (a + b) = 11 := by 
  rw [ha, hb] at h 
  norm_num at h 
  all_goals linarith