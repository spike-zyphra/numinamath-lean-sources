import Mathlib

open Real

theorem inequalities_106146 (a b x y : ℝ) :
    (a^2 + b^2) * (x^2 + y^2) ≥ |a * x + b * y| ^ 2 := by
  have h1 : |a * x + b * y| ^ 2 = (a * x + b * y) ^ 2 := by
    rw [sq_abs]
  rw [h1]
  nlinarith [sq_nonneg (a * y - b * x)]