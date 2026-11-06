import Mathlib

theorem algebra_93232 {x : ℝ} (hx : x = 1 / 10 ^ 1996) :
    3 / x > 3 + x ∧ 3 / x > 3 - x ∧ 3 / x > 3 * x ∧ 3 / x > x / 3 := by
  rw [hx]
  constructor
  · -- Show that 3 / x > 3 + x
    norm_num
  constructor
  · -- Show that 3 / x > 3 - x
    norm_num
  constructor
  · -- Show that 3 / x > 3 * x
    norm_num
  · -- Show that 3 / x > x / 3
    norm_num