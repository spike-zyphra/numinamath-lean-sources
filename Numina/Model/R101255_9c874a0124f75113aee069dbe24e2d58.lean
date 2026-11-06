import Mathlib

theorem algebra_270153 (x : ℝ) (h : (1/3)*x=12) : (1/4)*x=9 := by 
  have hx : x = 36 := by
    linarith [h]
  rw [hx]
  norm_num