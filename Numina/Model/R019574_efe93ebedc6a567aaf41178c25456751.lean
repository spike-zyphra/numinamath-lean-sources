import Mathlib

theorem inequalities_602491 (a b c : ℝ) :
    (a^2 + 2) * (b^2 + 2) * (c^2 + 2) ≥ 9 * (a * b + b * c + c * a) := by
  nlinarith [sq_nonneg (a * b * c - 1), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * b + b * c + c * a - 2), sq_nonneg (a + b + c),
          sq_nonneg (a * b * c), sq_nonneg (a * b + b * c + c * a),
          mul_self_nonneg (a * b - 1), mul_self_nonneg (b * c - 1), mul_self_nonneg (c * a - 1),
          mul_self_nonneg (a + b + c - 1)]