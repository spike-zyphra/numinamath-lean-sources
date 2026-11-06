import Mathlib

theorem algebra_21945 (x : ℝ) (h : 1200 * x = 1.5) :
    1000000 * x = 1250 := by
  have hx : x = (1.5 / 1200 : ℝ) := by 
    linarith
  rw [hx]
  norm_num