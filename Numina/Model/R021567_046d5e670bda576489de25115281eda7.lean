import Mathlib

theorem inequalities_603285 (x y : ℝ) (hy : 0 ≤ y) (h : y * (y + 1) ≤ (x + 1)^2) : y * (y - 1) ≤ x^2 := by 
  nlinarith [sq_nonneg (y - x - 1 / 2), sq_nonneg (x - y + 1 / 2), sq_nonneg (x - y), sq_nonneg (x + 1), sq_nonneg (y - 1), mul_nonneg hy (show 0 ≤ y from by linarith)]