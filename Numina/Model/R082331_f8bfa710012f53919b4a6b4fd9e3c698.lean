import Mathlib

theorem algebra_95192 {x : ℝ} (hx : x = 40) :
    (1.1 * x) * 0.9 = 39.60 := by 
  rw [hx]
  norm_num