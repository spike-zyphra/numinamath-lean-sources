import Mathlib

theorem algebra_278978 (v : ℝ) (h : v = 50) (t : ℝ) (ht : t = 30 / 60) : v * t = 25 := by 
  rw [h, ht]
  norm_num