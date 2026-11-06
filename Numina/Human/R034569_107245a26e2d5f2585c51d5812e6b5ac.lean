import Mathlib

theorem algebra_20375 (t : ℝ) (ht : t = 2.5) :
t + 7200 / 3600 = 4.5 := by
  rw [ht]
  norm_num