import Mathlib

theorem algebra_139365 (P : ℝ) (hP : P = 750000) (r : ℝ) (hr : r = 0.08) :
    P * (1 + r * 12) = 1470000 := by
  rw [hP, hr]
  norm_num