import Mathlib

theorem inequalities_154551 (a b c : ℝ) :
    a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]