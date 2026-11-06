import Mathlib

theorem algebra_196302 (a b : ℝ) (ha : a = 1 / 6) (hb : b = 2 / 6) :
    1 / (a + b) = 2 := by 
  rw [ha, hb]
  norm_num