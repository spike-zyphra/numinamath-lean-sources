import Mathlib

theorem algebra_1421 {a b : ℝ} (ha : a = -0.2) (hb : b = 0.04) :
    72 / 73 * (a ^ 2 - b) - 71 / 72 * (b + a + 0.16) - 1 / 4 * (a + b) = 0.04 := by
  rw [ha, hb]
  norm_num