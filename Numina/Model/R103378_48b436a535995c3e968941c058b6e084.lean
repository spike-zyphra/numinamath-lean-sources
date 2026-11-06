import Mathlib

theorem algebra_6461 {m b : ℝ} (h : m * 6 + b = 10) (h' : m * (-4) + b = 18) :
    -b / m = 18.5 := by 
  have eq1 : m = -4 / 5 := by 
    linarith 
  have eq2 : b = 74 / 5 := by 
    rw [eq1] at h 
    linarith 
  rw [eq1, eq2]
  norm_num