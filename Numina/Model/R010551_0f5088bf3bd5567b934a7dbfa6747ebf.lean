import Mathlib

theorem algebra_13751 (P : ℝ) (r : ℝ) (t : ℝ) (hP : P = 1000) (hr : r = 0.1) (ht : t = 3) :
    P * (1 + r) ^ t - P = 331 := by 
  rw [hP, hr, ht]
  norm_num