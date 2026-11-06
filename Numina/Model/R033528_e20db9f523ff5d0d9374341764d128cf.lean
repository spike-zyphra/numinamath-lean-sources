import Mathlib

theorem algebra_281682 {x : ℝ} (hx : x = 5.00) (h : 12 * x = y) :
    y = 60 := by 
  have eq1 : y = 12 * x := by
    linarith
  rw [eq1]
  rw [hx]
  norm_num