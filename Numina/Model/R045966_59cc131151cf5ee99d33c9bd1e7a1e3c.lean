import Mathlib

theorem inequalities_50818 (x : ℝ) (y : ℝ) (hx : 0 ≤ x) (hy : y^2 ≥ x * (x + 1)) :
    (y - 1)^2 ≥ x * (x - 1) := by 
  nlinarith [sq_nonneg (y - x - 1), sq_nonneg (y + 1 - x), sq_nonneg (y - 1), sq_nonneg (x - 1 / 2), mul_nonneg hx (show 0 ≤ x + 1 by linarith)]