import Mathlib

theorem inequalities_601692 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a^2 + b^2 + c^2 + 2 + (4/3) * (a^2 * b + b^2 * c + c^2 * a) ≥
    3 * (a * b + b * c + c * a) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
    sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
    mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc
    ]