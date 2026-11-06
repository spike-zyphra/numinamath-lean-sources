import Mathlib

theorem algebra_22239 {P r t : ℝ} (hP : P = 2000) (hr : r = 0.05) (ht : t = 18) :
    P * (1 + r * t) = 3800 := by 
  rw [hP, hr, ht]
  norm_num