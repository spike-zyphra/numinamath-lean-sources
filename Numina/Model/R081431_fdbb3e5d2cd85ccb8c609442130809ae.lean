import Mathlib

theorem inequalities_71651 (a b : ℝ) : 2*(a^4+a^2*b^2+b^4)≥3*(a^3*b+a*b^3) := by
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a - b), sq_nonneg (a * b), sq_nonneg (a + b), 
          sq_nonneg (a - b), sq_nonneg (a * b - b * a), sq_nonneg (a * b + b * a),
          sq_nonneg (a^2 + b^2 - a * b)]