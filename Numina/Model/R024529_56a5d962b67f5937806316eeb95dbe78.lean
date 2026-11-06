import Mathlib

theorem inequalities_7319 (a b c : ℝ) (h : a + b + c + 2 = a * b * c) :
    4 ≤ (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) := by
  nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b + c - a * b * c), sq_nonneg (a * b + b * c + c * a - 1),
          sq_nonneg (a * c - 1), sq_nonneg (b * a - 1), sq_nonneg (c * b - 1),
          sq_nonneg (a + b + c - 2)]