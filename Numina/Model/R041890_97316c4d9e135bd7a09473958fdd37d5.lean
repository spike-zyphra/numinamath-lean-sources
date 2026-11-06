import Mathlib

theorem inequalities_52375 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a^2 + b^2 + c^2 ≥ 3) :
    (a + b + c)^3 ≥ 9 * (a * b + b * c + c * a) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a + b + c - 3), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
            mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]