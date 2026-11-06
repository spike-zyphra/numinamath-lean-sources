import Mathlib

theorem algebra_16234 {x : ℝ} (hx : x = 25) :
    (2 / 5) * x = 10 := by
  rw [hx]
  norm_num