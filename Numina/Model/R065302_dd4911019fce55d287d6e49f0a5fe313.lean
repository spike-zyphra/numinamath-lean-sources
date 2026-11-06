import Mathlib

theorem algebra_21405 {x y : ℝ} (h : 3 * y = x) (h' : 2 * x + 5 * y = 11) :
    x + y = 4 := by
  have hx : x = 3 * y := by
    linarith 
  rw [hx] at h' 
  have hy : y = 1 := by
    linarith 
  have hx2 : x = 3 := by
    rw [hy] at hx 
    linarith 
  rw [hx2, hy] 
  all_goals norm_num