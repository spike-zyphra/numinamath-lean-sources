import Mathlib

theorem inequalities_6244
    (a b c : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hc : 0 ≤ c) :
    2 / 3 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥
    a ^ 3 * (b + c) + b ^ 3 * (a + c) + c ^ 3 * (a + b) := by
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
            sq_nonneg (a^2 - a*b), sq_nonneg (b^2 - b*c), sq_nonneg (c^2 - c*a),
            mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]