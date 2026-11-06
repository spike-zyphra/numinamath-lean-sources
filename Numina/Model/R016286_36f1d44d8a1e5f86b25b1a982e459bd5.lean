import Mathlib

theorem inequalities_277030 (a b c : ℝ) :
    a^2 + b^2 + c^2 ≥ a * b + a * c + b * c := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]