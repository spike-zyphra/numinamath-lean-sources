import Mathlib

theorem algebra_129609 (x : ℝ) (hx : 16.2 * ((4 + 1 / 7 - x * 700) / (1 + 2 / 7)) = 8.1) :
    x = 0.005 := by
  norm_num at hx ⊢
  linarith