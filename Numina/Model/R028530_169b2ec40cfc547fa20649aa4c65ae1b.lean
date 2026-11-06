import Mathlib

theorem algebra_104821 {x : ℝ} (hx : x = 470 * 14 + (600 - 470) * 11 - 600 * 12) :
    x = 810 := by
  rw [hx]
  norm_num