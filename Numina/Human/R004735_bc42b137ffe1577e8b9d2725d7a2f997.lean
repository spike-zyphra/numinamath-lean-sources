import Mathlib

theorem algebra_312693 {a b c : ℝ} (ha : a^2 + 2 * b = 7) (hb : b^2 - 2 * c = -1)
    (hc : c^2 - 6 * a = -17) : a + b + c = 3 := by
  nlinarith [sq_nonneg (a - 3), sq_nonneg (b + 1), sq_nonneg (c - 1)]