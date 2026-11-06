import Mathlib

theorem algebra_14728 (x : ℝ) (hx : 1.25 * (1 - x) = 1) : x = 0.2 := by
  norm_num at hx ⊢
  linarith