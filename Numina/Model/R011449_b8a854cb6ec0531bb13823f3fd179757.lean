import Mathlib

theorem algebra_94488 (messages minutes: ℝ) (hx : messages = 100) (hy : minutes = 30.5) :
20 + 0.05 * messages + 0.10 * (minutes - 30) * 60 = 28 := by 
  rw [hx, hy]
  norm_num