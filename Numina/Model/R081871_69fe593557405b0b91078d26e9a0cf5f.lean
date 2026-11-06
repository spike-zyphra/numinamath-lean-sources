import Mathlib

theorem algebra_259754 (x : ℝ) (hx : x = 2000) :
    (x * (1 + 50 / 100) ^ 6) = 22781.25 := by
  rw [hx]
  norm_num