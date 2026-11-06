import Mathlib

theorem inequalities_603915 (a b c d : ℝ) :
    a^2 * c^2 + a^2 * d^2 + b^2 * d^2 + b^2 * c^2 + 4 * a^2 * b^2 ≥ 4 * a^2 * b * d + 4 * a * b^2 * c := by
  nlinarith [sq_nonneg (a * c - b * d), sq_nonneg (a * d - b * c), 
          sq_nonneg (2 * a * b - a * c - b * d), 
          sq_nonneg (2 * a * b - a * d - b * c), 
          sq_nonneg (a * c + b * d - (a * d + b * c)), 
          sq_nonneg (a - b), sq_nonneg (c - d), 
          sq_nonneg (a * (c - d) - b * (c - d)), 
          sq_nonneg (b * (a - b) - a * (a - b)), 
          sq_nonneg (a * c + b * d), sq_nonneg (a * d + b * c), 
          sq_nonneg (2 * a * b - a * d - a * c), 
          sq_nonneg (2 * a * b - b * c - b * d)]