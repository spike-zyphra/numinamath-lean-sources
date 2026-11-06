import Mathlib

theorem inequalities_603192 (a b c : ℝ) : (a^2 + 2) * (b^2 + 2) * (c^2 + 2) ≥ 9 * (a * b + b * c + c * a) := by
  nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b + c - 3), sq_nonneg (a * b * c - 1),
          mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)), 
          mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (c - a)), 
          mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)), 
          sq_nonneg (a + b + c), sq_nonneg (a * b + b * c + c * a - 3)]