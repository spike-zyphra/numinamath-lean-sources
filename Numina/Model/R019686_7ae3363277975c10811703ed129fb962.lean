import Mathlib

theorem algebra_12933 {a c : ℝ} (ha : 6 * a ^ 2 + 2 * a + 13 = 0) (hc : 54 + 6 * (2 * c + 1) + 52 * c ^ 2 + 13 = -52 * c)
    (h : 2 * c + 1 ≠ 0) : (3 * a + 3) / (2 * c + 1) + a = 11 / 6 := by
  have h2 : 6 * a ^ 2 + 2 * a + 13 > 0 := by
    nlinarith [sq_nonneg (a + 1 / 6), sq_nonneg (c + 1 / 2)]
  nlinarith