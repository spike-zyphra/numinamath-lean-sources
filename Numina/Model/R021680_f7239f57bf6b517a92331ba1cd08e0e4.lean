import Mathlib

theorem algebra_302861 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 + a * b * c = 4) : a + b + c ≤ 3 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a + b + c - 3),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos (show 0 < a * b by nlinarith) (show 0 < c by linarith),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]