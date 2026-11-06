import Mathlib

theorem inequalities_597725 (a b c : ℝ) :
    a^4 * (b^2 + c^2) + b^4 * (c^2 + a^2) + c^4 * (a^2 + b^2) +
    2 * a * b * c * (a^2 * b + a^2 * c + b^2 * a + b^2 * c + c^2 * a + c^2 * b - a^3 - b^3 - c^3 - 3 * a * b * c) ≥
    2 * (a^3 * b^3 + b^3 * c^3 + c^3 * a^3) := by
  nlinarith [sq_nonneg (a^2 * b - a^2 * c - b^2 * a + b^2 * c + c^2 * a - c^2 * b),
          sq_nonneg (a * b - a * c - b * c + c * a + b * a - c * b),
          sq_nonneg (a * (a - b) + a * (a - c) + b * (b - c) + b * (b - a) + c * (c - a) + c * (c - b)), 
          sq_nonneg (a * b - a * c), sq_nonneg (a * b - b * c), sq_nonneg (a * c - b * c),
          sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), 
          sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          sq_nonneg (a * b), sq_nonneg (a * c), sq_nonneg (b * c)]