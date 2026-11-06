import Mathlib

theorem algebra_3274 {x : ℝ} (h : 3 * x ^ 2 + 7 * x + 5 = 2 + x) : x ^ 3 + x ^ 2 - x + 6 = 7 := by 
  have hx : (x + 1) ^ 2 = 0 := by 
    linarith 
  have hx2 : x + 1 = 0 := by 
    rw [sq_eq_zero_iff] at hx 
    exact hx 
  have hx3 : x = -1 := by 
    linarith 
  rw [hx3] 
  norm_num