import Mathlib

theorem algebra_138669 {a b : ℝ} (ha : a = 2) (hb : b = 1 / 2) : a / b = 4 := by 
  rw [ha, hb]
  norm_num