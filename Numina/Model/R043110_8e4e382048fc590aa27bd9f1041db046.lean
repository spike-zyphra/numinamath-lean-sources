import Mathlib

theorem inequalities_66473 (a b c d e : ℝ) :
    a^2 + b^2 + c^2 + d^2 + e^2 ≥ a * (b + c + d + e) := by 
  nlinarith [sq_nonneg (b - a / 2), sq_nonneg (c - a / 2), sq_nonneg (d - a / 2),
          sq_nonneg (e - a / 2), sq_nonneg (a - (b + c + d + e) / 2)]