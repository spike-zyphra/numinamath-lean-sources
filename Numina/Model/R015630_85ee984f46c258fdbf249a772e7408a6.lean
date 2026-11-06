import Mathlib

theorem inequalities_596844 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a^2 + b^2 + c^2 = 8) : 4 * (a + b + c - 4) ≤ a * b * c := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a + b + c - 4), sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2),
          mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc
          ]