import Mathlib

theorem algebra_21738 (a b c : ℝ) (ha : a = 10) (hb : b = 12) (hc : c = 1.5):
    (a * b - (a - 2 * c) * (b - 2 * c)) / (a * b) = 19 / 40 := by
  rw [ha, hb, hc]
  norm_num