import Mathlib

theorem algebra_20759 {x : ℝ} (hx : x = 97969) : (Real.sqrt x) ^ 2 = x := by 
  rw [hx]
  exact Real.sq_sqrt (by norm_num)