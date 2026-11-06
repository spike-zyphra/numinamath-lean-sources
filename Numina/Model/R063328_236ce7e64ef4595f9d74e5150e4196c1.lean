import Mathlib

theorem inequalities_8116 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c ≥ a * b * c) : a^2 + b^2 + c^2 ≥ a * b * c := by
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
            sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
            mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]