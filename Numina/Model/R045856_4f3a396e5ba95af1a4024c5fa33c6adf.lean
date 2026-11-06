import Mathlib

theorem inequalities_601480 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (1 + a) * (1 + b) * (1 + c) = 8) : a * b * c ≤ 1 := by
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1)]