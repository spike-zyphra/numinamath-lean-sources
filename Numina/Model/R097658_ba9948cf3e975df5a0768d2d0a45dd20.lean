import Mathlib

theorem algebra_167855 (x : ℝ) (hx : x = 20) :
    (x * (1 - 80 / 100)) / (1 - 20 / 100) = 5 := by
  rw [hx]
  norm_num