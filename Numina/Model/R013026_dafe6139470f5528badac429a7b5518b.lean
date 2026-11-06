import Mathlib

theorem inequalities_38349 (a b c : ℝ) (h : a^3 * (b + c) + b^3 * (a + c) + c^3 * (a + b) = 0) :
    a * b + b * c + c * a ≤ 0 := by
  nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c),
          sq_nonneg (a * b + b * c + c * a),
          sq_nonneg (a * (a + b + c)), sq_nonneg (b * (a + b + c)), sq_nonneg (c * (a + b + c)),
          sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2)]