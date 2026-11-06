import Mathlib

theorem inequalities_103592 (a b c : ℝ) :
    2 * (a^4 + b^4 + c^4) ≥ a^3 * b + b^3 * c + c^3 * a + a * b^3 + b * c^3 + c * a^3 := by 
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a*(a - b)), sq_nonneg (b*(b - c)), sq_nonneg (c*(c - a)),
          sq_nonneg (a*(a - c)), sq_nonneg (b*(b - a)), sq_nonneg (c*(c - b)),
          sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]