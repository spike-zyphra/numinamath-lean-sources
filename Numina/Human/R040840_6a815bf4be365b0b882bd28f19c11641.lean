import Mathlib

theorem inequalities_110766 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^2 * b + b^2 * c + c^2 * a) * (a * b^2 + b * c^2 + c * a^2) ≥ 9 * a^2 * b^2 * c^2 := by 
  nlinarith [sq_nonneg (a^2 * b - b^2 * c), sq_nonneg (b^2 * c - c^2 * a), sq_nonneg (c^2 * a - a^2 * b),
    sq_nonneg (a * b^2 - b * c^2), sq_nonneg (b * c^2 - c * a^2), sq_nonneg (c * a^2 - a * b^2),
    mul_self_nonneg (a - b), mul_self_nonneg (b - c), mul_self_nonneg (c - a),
    mul_self_nonneg (a - b * c), mul_self_nonneg (b - c * a), mul_self_nonneg (c - a * b),
    mul_self_nonneg (a * b - c), mul_self_nonneg (b * c - a), mul_self_nonneg (c * a - b),
    mul_self_nonneg (a - 1), mul_self_nonneg (b - 1), mul_self_nonneg (c - 1),
    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]