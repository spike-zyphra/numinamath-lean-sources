import Mathlib

theorem inequalities_205080 (a b c : ℝ) :
    (a + b) * (a + b - 2 * c) + (b + c) * (b + c - 2 * a) +
    (c + a) * (c + a - 2 * b) ≥ 0 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
          sq_nonneg (a - b + c), sq_nonneg (a + b - c)]