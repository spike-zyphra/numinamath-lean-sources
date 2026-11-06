import Mathlib

theorem algebra_19821 {x : ℝ} (hx : x = 60) :
    (x * 0.05 - (x * 0.8) * 0.05) * 100 = 60 := by
  rw [hx]
  norm_num