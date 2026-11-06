import Mathlib

theorem inequalities_71645 (a b c : ℝ) :
    (a * b + b * c + c * a - 1) ^ 2 ≤ (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) := by
  nlinarith [sq_nonneg (a * b * c - a - b - c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a * c - b), sq_nonneg (b * a - c),
          sq_nonneg (c * b - a)]