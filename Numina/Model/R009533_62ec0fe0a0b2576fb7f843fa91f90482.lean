import Mathlib

theorem algebra_21926 (x : ℝ) (hx : x = 244) :
    round (x * (1 - 1 / 100)^10) = 221 := by
  rw [hx]
  norm_num [round_eq]
  <;> norm_num