import Mathlib

theorem inequalities_603402 (a b c : ℝ) :
    a^6 + b^6 + c^6 + a^2 * b^2 * c^2 ≥ 2/3 * (a^5 * (b + c) + b^5 * (c + a) + c^5 * (a + b)) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b + c),
          sq_nonneg (a - b + c), sq_nonneg (a + b - c), sq_nonneg (a - b - c),
          sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
          sq_nonneg (a^3 - b^3), sq_nonneg (b^3 - c^3), sq_nonneg (c^3 - a^3),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          sq_nonneg (a * (b - c)), sq_nonneg (b * (a - c)), sq_nonneg (c * (a - b)),
          sq_nonneg (a^2 + b^2 + c^2 - a * b - b * c - c * a)]